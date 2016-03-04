{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -fno-warn-missing-methods #-}

module Advanced where

import Data.IORef

import Control.Monad.Operational.Higher



-- This file is a version of `Simple.hs` where we want to expose the fact that
-- programs have expressions as sub-structures. To do this, we use instructions
-- with types of the form
--
--     instr (Param2 p e) a
--
-- where `p` represents sub-programs and `e` represents expressions.
--
-- The `Program` type is now specialized to `Program ... '[Exp]`.
--
-- By exposing expressions in this way, we decouple the interpretation of
-- instructions from that of expressions. This can be seen in the example below
-- which defines
--
--     main = fmap eval $ interpretBi (return . eval) prog
--
-- The interpretation of instructions is obtained from the `InterpBi` class,
-- while the interpretation of expressions is provided separately.



--------------------------------------------------------------------------------
-- Simple expression language
--------------------------------------------------------------------------------

data Exp a
  where
    Lit :: a -> Exp a
    Add :: Num a => Exp a -> Exp a -> Exp a
    Eq  :: Eq a => Exp a -> Exp a -> Exp Bool

instance Num a => Num (Exp a)
  where
    fromInteger = Lit . fromInteger
    (+) = Add

eval :: Exp a -> a
eval (Lit i)   = i
eval (Add a b) = eval a + eval b
eval (Eq a b)  = eval a == eval b



--------------------------------------------------------------------------------
-- Composable instructions
--------------------------------------------------------------------------------

data Val a = Val a

-- | If statement
data If fs a
  where
    If :: e Bool -> p a -> p a -> If (Param2 p e) a

-- | Loop
data Loop fs a
  where
    Loop :: e Int -> p () -> Loop (Param2 p e) ()

-- | Mutable references
data Ref fs a
  where
    NewRef :: e a -> Ref (Param2 p e) (IORef a)
    GetRef :: IORef a -> Ref (Param2 p e) (Val a)
    SetRef :: IORef a -> e a -> Ref (Param2 p e) ()
  -- Note: `GetRef` cannot return `exp a` as that would prevent writing the
  -- `HBifunctor` instance.

instance HFunctor If
  where
    hfmap f (If c thn els) = If c (f thn) (f els)

instance HFunctor Loop
  where
    hfmap f (Loop n body) = Loop n (f body)

instance HFunctor Ref
  where
    hfmap f (NewRef a)   = NewRef a
    hfmap f (GetRef r)   = GetRef r
    hfmap f (SetRef r a) = SetRef r a

instance HBifunctor If
  where
    hbimap f g (If c thn els) = If (g c) (f thn) (f els)

instance HBifunctor Loop
  where
    hbimap f g (Loop n body) = Loop (g n) (f body)

instance HBifunctor Ref
  where
    hbimap _ g (NewRef a)   = NewRef (g a)
    hbimap _ g (GetRef r)   = GetRef r
    hbimap _ g (SetRef r a) = SetRef r (g a)

instance InterpBi If IO fs
  where
    interpBi (If c thn els) = c >>= \c' -> if c' then thn else els

instance InterpBi Loop IO fs
  where
    interpBi (Loop n body) = n >>= \n' -> replicateM_ n' body

instance InterpBi Ref IO fs
  where
    interpBi (NewRef a)   = newIORef =<< a
    interpBi (GetRef r)   = fmap Val $ readIORef r
    interpBi (SetRef r a) = writeIORef r =<< a



--------------------------------------------------------------------------------
-- Example
--------------------------------------------------------------------------------

type MyProgram a = Program (If :+: Loop :+: Ref) (Param1 Exp) a

iff :: Exp Bool -> MyProgram a -> MyProgram a -> MyProgram a
iff c thn els = singleInj $ If c thn els

loop :: Exp Int -> MyProgram () -> MyProgram ()
loop n = singleInj . Loop n

newRef :: Exp a -> MyProgram (IORef a)
newRef = singleInj . NewRef

getRef :: IORef a -> MyProgram (Exp a)
getRef r = do
    Val a <- singleInj $ GetRef r
    return $ Lit a

setRef :: IORef a -> Exp a -> MyProgram ()
setRef r = singleInj . SetRef r

prog :: MyProgram (Exp Int)
prog = do
    r <- newRef 0
    loop 10 $ do
        a <- getRef r
        iff (Eq a 3)
            (setRef r 100)
            (setRef r (a+1))
    getRef r

main = fmap eval $ interpretBi (return . eval) prog

