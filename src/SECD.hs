{-# LANGUAGE TemplateHaskell #-}

module SECD where

import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.State
import           Data.Map.Strict      as Map (Map (..), empty, fromList, lookup,
                                              null)
import           Data.Stack           (Stack (..), stackNew, stackPop,
                                       stackPush)
import           Data.Vector          as Vec (Vector (..), empty, snoc, (!?))
import           Data.Void            (Void)
import           Prelude              hiding (lookup, null)

import           Lens.Micro
import           Lens.Micro.TH

data Value
  = IntValue Int
  | BoolValue Bool
  | CharValue Char
  | DoubleValue Double
  | FunValue Code Context
  | ListValue [Value]
  deriving (Eq, Show)

data SECDError
  = WrongLevel
  | UnknownVar
  | EmptyStack
  | NoReturnState
  | EmptyContext
  | TypeError
  | RuntimeError
  deriving (Eq, Show)

data ContextEntry
  = M (Map Var Value)
  | Omega
  deriving (Eq, Show)

type Var = Int
type Level = Int
type Code = Vector Command
type Context = Vector ContextEntry

type S = Stack Value
type E = Context
type C = Code
type D = Stack SECDDump

data Command
  = LD Level Var
  | LDC Value
  | LDF Code
  | NIL
  | CAR
  | CDR
  | CONS
  | AP
  | RET
  | SEL Code Code
  | JOIN
  | RAP
  | DUM
  deriving (Eq, Show)

data SECDDump = SECDDump
  {
    _sDump :: S,
    _eDump :: E,
    _cDump :: C
  }
  deriving (Show)

makeLenses ''SECDDump

data SECDState = SECDState
  {
    _s :: S,
    _e :: E,
    _c :: C,
    _d :: D
  }
  deriving (Show)

makeLenses ''SECDState

type SECDMonad = ExceptT SECDError (StateT SECDState IO)

stdEnv :: E
stdEnv = Vec.empty

initialState :: SECDState
initialState = SECDState stackNew stdEnv Vec.empty stackNew

interpreterCmd :: Command -> SECDMonad ()
interpreterCmd (LD level var)    = do
  st <- get
  case (st ^. e) !? level of
    Nothing -> throwError WrongLevel
    Just (M slice) -> case lookup var slice of
      Nothing  -> throwError UnknownVar
      Just val -> put $ st & s %~ (flip stackPush val)
    Just _ -> throwError TypeError
interpreterCmd (LDC val)         = do
  st <- get
  put $ st & s %~ (flip stackPush val)
interpreterCmd (LDF code)        = do
  st <- get
  put $ st & s %~ (flip stackPush (FunValue code (st ^. e)))
interpreterCmd NIL = do
  st <- get
  put $ st & s %~ (flip stackPush $ ListValue [])
interpreterCmd CAR = do
  st <- get
  case stackPop (st ^. s) of
    Nothing -> throwError EmptyStack
    Just (stack, ListValue []) -> throwError RuntimeError
    Just (stack, ListValue (x:xs)) ->
      put $ st & s .~ (stackPush stack x)
interpreterCmd CDR = do
  st <- get
  case stackPop (st ^. s) of
    Nothing -> throwError EmptyStack
    Just (stack, ListValue []) -> throwError RuntimeError
    Just (stack, ListValue (x:xs)) ->
      put $ st & s .~ (stackPush stack $ ListValue xs)
interpreterCmd CONS = do
  st <- get
  case stackPop (st ^. s) of
    Nothing -> throwError EmptyStack
    Just (stack, ListValue lst1) ->
      case stackPop stack of
        Nothing -> throwError EmptyStack
        Just (stack', ListValue lst2) ->
          put $ st & s .~ (stackPush stack' $ ListValue $ lst1 ++ lst2)
        Just (_, _) -> throwError TypeError
    Just (_, _) -> throwError TypeError
interpreterCmd AP                = do
  st <- get
  case stackPop (st ^. s) of
    Nothing -> throwError EmptyStack
    Just (stack, FunValue code context) ->
      case stackPop stack of
        Nothing -> throwError EmptyStack
        Just (stack', ListValue paramlist) ->
          put $ SECDState stackNew
                          (snoc context (M $ fromList $ zip [1..] $ paramlist))
                          code
                          (stackPush (st ^. d) (SECDDump (st ^. s)
                                                         (st ^. e)
                                                         (st ^. c)))
        Just (_, _) -> throwError TypeError
    Just (_, _) -> throwError TypeError
interpreterCmd RET               = do
  st <- get
  case stackPop (st ^. s) of
    Nothing -> throwError EmptyStack
    Just (_, head) -> case stackPop (st ^. d) of
      Nothing -> throwError NoReturnState
      Just (stack', head') ->
        put $ SECDState (stackPush (head' ^. sDump) head)
                        (head' ^. eDump)
                        (head' ^. cDump)
                        stack'
interpreterCmd (SEL code1 code2) = do
  st <- get
  case stackPop (st ^. s) of
    Nothing -> throwError EmptyStack
    Just (stack, head) -> case head of
      BoolValue True ->
        put $ SECDState stack
                        (st ^. e)
                        code1
                        (stackPush (st ^. d) (SECDDump (st ^. s)
                                                       (st ^. e)
                                                       (st ^. c)))
      BoolValue False ->
        put $ SECDState stack
                        (st ^. e)
                        code2
                        (stackPush (st ^. d) (SECDDump (st ^. s)
                                                       (st ^. e)
                                                       (st ^. c)))
      _ -> throwError TypeError
interpreterCmd JOIN              = do
  st <- get
  case stackPop (st ^. d) of
    Nothing -> throwError NoReturnState
    Just (stack, head) ->
      put $ SECDState (st ^. s)
                      (st ^. e)
                      (head ^. cDump)
                      stack
interpreterCmd RAP               = do
  st <- get
  case stackPop (st ^. s) of
    Nothing -> throwError EmptyStack
    Just (stack, FunValue code context) ->
      case stackPop stack of
        Nothing -> throwError EmptyStack
        Just (stack', ListValue paramlist) ->
          case (st ^. e) !? (length (st ^. e) - 1) of
            Nothing -> throwError EmptyContext
            Just Omega ->
              put $ SECDState stackNew
                              (fmap (let p Omega = True
                                         p _     = False
                                     in  \x -> if p x
                                       then (M $ fromList $ zip [1..] $ paramlist)
                                       else x)
                                    context)
                              code
                              (stackPush (st ^. d) (SECDDump stack (st ^. e) (st ^. c)))
            Just _ -> throwError TypeError
        Just (_, _) -> throwError TypeError
    Just (_, _) -> throwError TypeError
interpreterCmd DUM               = do
  st <- get
  put $ st & e %~ (flip snoc Omega)

evalNextCmd :: SECDMonad ()
evalNextCmd = do
  st <- get
  case (st ^. c) !? 0 of
    Nothing  -> return ()
    Just cmd -> interpreterCmd cmd

evalCmds :: SECDMonad ()
evalCmds = do
  st <- get
  mapM_ interpreterCmd (st ^. c)
