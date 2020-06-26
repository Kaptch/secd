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

data SECDState = SECDState
  {
    s :: S,
    e :: E,
    c :: C,
    d :: D
  }

data SECDDump = SECDDump
  {
    sDump :: S,
    eDump :: E,
    cDump :: C
  }

type SECDMonad = ExceptT SECDError (StateT SECDState IO)

stdEnv :: E
stdEnv = Vec.empty

initialState :: SECDState
initialState = SECDState { s = stackNew,
                           e = stdEnv,
                           c = Vec.empty,
                           d = stackNew
                         }

interpreterCmd :: Command -> SECDMonad ()
interpreterCmd (LD level var)    = do
  st <- get
  case (e st) !? level of
    Nothing -> throwError WrongLevel
    Just (M slice) -> case lookup var slice of
      Nothing  -> throwError UnknownVar
      Just val -> put $ SECDState { s = stackPush (s st) val,
                                    e = e st,
                                    c = c st,
                                    d = d st
                                  }
    Just _ -> throwError TypeError
interpreterCmd (LDC val)         = do
  st <- get
  put $ SECDState { s = stackPush (s st) val,
                    e = e st,
                    c = c st,
                    d = d st
                  }
interpreterCmd (LDF code)        = do
  st <- get
  put $ SECDState { s = stackPush (s st) (FunValue code (e st)),
                    e = e st,
                    c = c st,
                    d = d st
                  }
interpreterCmd NIL = do
  st <- get
  put $ SECDState { s = stackPush (s st) $ ListValue [],
                    e = e st,
                    c = c st,
                    d = d st
                  }
interpreterCmd CAR = do
  st <- get
  case stackPop (s st) of
    Nothing -> throwError EmptyStack
    Just (stack, ListValue []) -> throwError RuntimeError
    Just (stack, ListValue (x:xs)) ->
      put $ SECDState { s = stackPush stack x,
                        e = e st,
                        c = c st,
                        d = d st
                      }
interpreterCmd CDR = do
  st <- get
  case stackPop (s st) of
    Nothing -> throwError EmptyStack
    Just (stack, ListValue []) -> throwError RuntimeError
    Just (stack, ListValue (x:xs)) ->
      put $ SECDState { s = stackPush stack $ ListValue xs,
                        e = e st,
                        c = c st,
                        d = d st
                      }
interpreterCmd CONS = do
  st <- get
  case stackPop (s st) of
    Nothing -> throwError EmptyStack
    Just (stack, ListValue lst1) ->
      case stackPop stack of
        Nothing -> throwError EmptyStack
        Just (stack', ListValue lst2) ->
          put $ SECDState { s = stackPush stack' $ ListValue $ lst1 ++ lst2,
                            e = e st,
                            c = c st,
                            d = d st
                          }
        Just (_, _) -> throwError TypeError
    Just (_, _) -> throwError TypeError
interpreterCmd AP                = do
  st <- get
  case stackPop (s st) of
    Nothing -> throwError EmptyStack
    Just (stack, FunValue code context) ->
      case stackPop stack of
        Nothing -> throwError EmptyStack
        Just (stack', ListValue paramlist) ->
          put $ SECDState { s = stackNew,
                            e = snoc context (M $ fromList $ zip [1..] $ paramlist),
                            c = code,
                            d = stackPush (d st) (SECDDump (s st) (e st) (c st))
                          }
        Just (_, _) -> throwError TypeError
    Just (_, _) -> throwError TypeError
interpreterCmd RET               = do
  st <- get
  case stackPop (s st) of
    Nothing -> throwError EmptyStack
    Just (_, head) -> case stackPop (d st) of
      Nothing -> throwError NoReturnState
      Just (stack', head') ->
        put $ SECDState { s = stackPush (sDump head') head,
                          e = eDump head',
                          c = cDump head',
                          d = stack'
                        }
interpreterCmd (SEL code1 code2) = do
  st <- get
  case stackPop (s st) of
    Nothing -> throwError EmptyStack
    Just (stack, head) -> case head of
      BoolValue True ->
        put $ SECDState { s = stack,
                          e = e st,
                          c = code1,
                          d = stackPush (d st) (SECDDump (s st) (e st) (c st))
                        }
      BoolValue False ->
        put $ SECDState { s = stack,
                          e = e st,
                          c = code2,
                          d = stackPush (d st) (SECDDump (s st) (e st) (c st))
                        }
      _ -> throwError TypeError
interpreterCmd JOIN              = do
  st <- get
  case stackPop (d st) of
    Nothing -> throwError NoReturnState
    Just (stack, head) ->
      put $ SECDState { s = s st,
                        e = e st,
                        c = cDump head,
                        d = stack
                      }
interpreterCmd RAP               = do
  st <- get
  case stackPop (s st) of
    Nothing -> throwError EmptyStack
    Just (stack, FunValue code context) ->
      case stackPop stack of
        Nothing -> throwError EmptyStack
        Just (stack', ListValue paramlist) ->
          case (e st) !? (length (e st) - 1) of
            Nothing -> throwError EmptyContext
            Just Omega ->
              put $ SECDState { s = stackNew,
                                e = fmap (let p Omega = True
                                              p _     = False
                                          in  \x -> if p x
                                            then (M $ fromList $ zip [1..] $ paramlist)
                                            else x)
                                    context,
                                c = code,
                                d = stackPush (d st) (SECDDump stack (e st) (c st))
                              }
            Just _ -> throwError TypeError
        Just (_, _) -> throwError TypeError
    Just (_, _) -> throwError TypeError
interpreterCmd DUM               = do
  st <- get
  put $ SECDState { s = s st,
                    e = snoc (e st) Omega,
                    c = c st,
                    d = d st
                  }

interpreter :: SECDMonad ()
interpreter = do
  st <- get
  mapM_ interpreterCmd (c st)
