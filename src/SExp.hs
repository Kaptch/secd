module SExp where

data SExp a
  = Atom a
  | Cons (SExp a) (SExp a)
  deriving (Eq, Show)

instance Functor SExp where
  fmap f (Atom a)           = Atom $ f a
  fmap f (Cons sexp1 sexp2) = Cons (fmap f sexp1) (fmap f sexp2)

instance Applicative SExp where
  pure = Atom
  (<*>) f a = f >>= (\x -> a >>= (return . x))

instance Monad SExp where
  return = pure
  (>>=) (Atom a) f           = f a
  (>>=) (Cons sexp1 sexp2) f = Cons (sexp1 >>= f) (sexp2 >>= f)

cons :: SExp a -> SExp a -> SExp a
cons = Cons

car :: SExp a -> Maybe (SExp a)
car (Atom _)       = Nothing
car (Cons sexp1 _) = Just sexp1

cdr :: SExp a -> Maybe (SExp a)
cdr (Atom _)       = Nothing
cdr (Cons _ sexp2) = Just sexp2
