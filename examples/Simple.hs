{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -fno-warn-missing-methods #-}

module Simple where

import Data.IORef

import Control.Monad.Operational.Higher



-- This file demonstrates simple use of the library. Instructions have types of
-- the form
--
--     instr '[p] a
--
-- where `p` represents sub-programs.
--
-- The `Program` type is specialized to `Program ... '[]`, which means that
-- we're not interested in exposing any sub-structures of programs.



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

-- | If statement
data If p a
  where
    If :: Exp Bool -> p a -> p a -> If (Param1 p) a

-- | Loop
data Loop p a
  where
    Loop :: Exp Int -> p () -> Loop (Param1 p) ()

-- | Mutable references
data Ref p a
  where
    NewRef :: Exp a -> Ref (Param1 p) (IORef a)
    GetRef :: IORef a -> Ref (Param1 p) (Exp a)
    SetRef :: IORef a -> Exp a -> Ref (Param1 p) ()

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

instance Interp If IO fs
  where
    interp (If c thn els) = if eval c then thn else els

instance Interp Loop IO fs
  where
    interp (Loop n body) = replicateM_ (eval n) body

instance Interp Ref IO fs
  where
    interp (NewRef a)   = newIORef (eval a)
    interp (GetRef r)   = fmap Lit $ readIORef r
    interp (SetRef r a) = writeIORef r (eval a)



--------------------------------------------------------------------------------
-- Example
--------------------------------------------------------------------------------

type MyProgram = Program (If :+: Loop :+: Ref) Param0

iff :: Exp Bool -> MyProgram a -> MyProgram a -> MyProgram a
iff c thn els = singleInj $ If c thn els

loop :: Exp Int -> MyProgram () -> MyProgram ()
loop n = singleInj . Loop n

newRef :: Exp a -> MyProgram (IORef a)
newRef = singleInj . NewRef

getRef :: IORef a -> MyProgram (Exp a)
getRef = singleInj . GetRef

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

main = fmap eval $ interpret prog

