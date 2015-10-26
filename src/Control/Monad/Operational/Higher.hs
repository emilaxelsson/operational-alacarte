{-# LANGUAGE CPP #-}

-- | = Introduction
--
-- This module gives an alternative to the Operational package \[1\], in which
-- instructions are higher-order functors, parameterized on the program monad
-- that they are part of. This makes it possible to define instruction sets
-- compositionally using ':+:'. In the normal Operational, this can be done for
-- simple instructions, but here it can be done even for \"control
-- instructions\" -- instructions that take program as arguments.
--
-- For general information about the ideas behind this module, see the
-- Operational package: <http://hackage.haskell.org/package/operational>
--
-- = Example
--
-- (Full code found in
-- <https://github.com/emilaxelsson/operational-alacarte/blob/master/examples/Simple.hs>.)
--
-- An \"if\" instruction can be defined as follows:
--
-- @
-- data If p a where
--   If :: Exp `Bool` -> p a -> p a -> If p a
-- @
--
-- Note the use of the type parameter @p@ to refer to sub-programs. (@Exp@ is
-- some type representing pure expressions.)
--
-- We can now make program types that combine several instructions; e.g.:
--
-- @type MyProgram a = `Program` (If `:+:` Loop `:+:` ...) a@
--
-- Here the sub-programs of @If@ (and @Loop@, etc.) will have the type
-- @MyProgram@. With the original Operational package, we would have to
-- hard-code a specific type for the sub-programs of @If@ (or make @MyProgram@ a
-- recursive newtype, as noted by the author of Operational).
--
-- Interpretation of 'Program' can be done using
--
-- @`interpret` :: (`Interp` i m, `HFunctor` i, `Monad` m) => `Program` i a -> m a@
--
-- In order to use this function, @If@ needs to be an instance of 'Interp' and
-- 'HFunctor'. The 'HFunctor' instance is straightforward:
--
-- @
-- instance `HFunctor` If where
--   `hfmap` f (If c thn els) = If c (f thn) (f els)
-- @
--
-- The 'Interp' type class is parameterized both on the instruction and the
-- destination monad. For example, interpretation of @If@ in the IO monad might
-- look as follows:
--
-- @
-- instance `Interp` If `IO` where
--   `interp` (If c thn els) = if eval c then thn else els
-- @
--
-- (Here @eval@ is the evaluator for the expression languauge @Exp@.)
--
-- The 'Interp' class distributes over ':+:' which means that it is possible to
-- interpret any expression type @(I1 `:+:` I2 `:+:` I3 `:+:` ...)@ to 'IO', as
-- long as the individual instructions (@I1@, @I2@, etc.) have 'Interp'
-- instances for 'IO'.

module Control.Monad.Operational.Higher
    ( module Control.Monad
    , module Data.ALaCarte
      -- * Program monad
    , ProgramT
    , Program
    , singleton
    , singleInj
      -- * Interpretation
    , liftProgram
    , interpretWithMonadT
    , interpretWithMonad
    , Interp (..)
    , interpretT
    , interpret
    , ProgramViewT (..)
    , ProgramView (..)
    , viewT
    , view
    , unview
      -- * Instructions parameterized on expression language
    , IExp
    , injE
    , prjE
    , singleE
    ) where



#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Trans
import Data.Typeable

import Data.ALaCarte



----------------------------------------------------------------------------------------------------
-- * Program monad
----------------------------------------------------------------------------------------------------

-- | Representation of programs parameterized by the primitive instructions
data ProgramT instr m a
  where
    Lift  :: m a -> ProgramT instr m a
    Bind  :: ProgramT instr m a -> (a -> ProgramT instr m b) -> ProgramT instr m b
    Instr :: instr (ProgramT instr m) a -> ProgramT instr m a
#if  __GLASGOW_HASKELL__>=708
  deriving Typeable
#endif

-- | Representation of programs parameterized by its primitive instructions
type Program instr = ProgramT instr Identity

instance Monad m => Functor (ProgramT instr m)
  where
    fmap = liftM

instance Monad m => Applicative (ProgramT instr m)
  where
    pure  = return
    (<*>) = ap

instance Monad m => Monad (ProgramT instr m)
  where
    return = Lift . return
    (>>=)  = Bind

instance MonadTrans (ProgramT instr)
  where
    lift = Lift

-- | Make a program from a single primitive instruction
singleton :: instr (ProgramT instr m) a -> ProgramT instr m a
singleton = Instr

-- | Make a program from a single primitive instruction
singleInj :: (i :<: instr) => i (ProgramT instr m) a -> ProgramT instr m a
singleInj = Instr . inj



----------------------------------------------------------------------------------------------------
-- * Interpretation
----------------------------------------------------------------------------------------------------

-- | Lift a simple program to a program over a monad @m@
liftProgram :: forall instr m a . (HFunctor instr, Monad m) => Program instr a -> ProgramT instr m a
liftProgram = go
  where
    go :: Program instr b -> ProgramT instr m b
    go (Lift a)   = Lift $ return $ runIdentity a
    go (Bind p k) = Bind (go p) (go . k)
    go (Instr i)  = Instr $ hfmap go i

-- | Interpret a program in a monad
interpretWithMonadT :: forall instr m n a . (HFunctor instr, Monad m)
    => (forall b . instr m b -> m b)
    -> (forall b . n b -> m b)
    -> ProgramT instr n a -> m a
interpretWithMonadT runi runn = go
  where
    go :: ProgramT instr n b -> m b
    go (Lift a)   = runn a
    go (Bind p k) = go p >>= (go . k)
    go (Instr i)  = runi $ hfmap go i

-- | Interpret a program in a monad
interpretWithMonad :: (HFunctor instr, Monad m) =>
    (forall b . instr m b -> m b) -> Program instr a -> m a
interpretWithMonad interp = interpretWithMonadT interp (return . runIdentity)

-- | @`Interp` i m@ represents the fact that @i@ can be interpreted in the monad @m@
class Interp i m
  where
    -- | Interpret an instruction in a monad
    interp :: i m a -> m a

instance (Interp i1 m, Interp i2 m) => Interp (i1 :+: i2) m
  where
    interp (Inl i) = interp i
    interp (Inr i) = interp i

-- | Interpret a program in a monad. The interpretation of primitive instructions is provided by the
-- 'Interp' class.
interpretT :: (Interp i m, HFunctor i, Monad m) => (forall b . n b -> m b) -> ProgramT i n a -> m a
interpretT = interpretWithMonadT interp

-- | Interpret a program in a monad. The interpretation of primitive instructions is provided by the
-- 'Interp' class.
interpret :: (Interp i m, HFunctor i, Monad m) => Program i a -> m a
interpret = interpretWithMonad interp

-- | View type for inspecting the first instruction
data ProgramViewT instr m a
  where
    Return :: a -> ProgramViewT instr m a
    (:>>=) :: instr (ProgramT instr m) b -> (b -> ProgramT instr m a) -> ProgramViewT instr m a

-- | View type for inspecting the first instruction
type ProgramView instr = ProgramViewT instr Identity

-- | View function for inspecting the first instruction
viewT :: Monad m => ProgramT instr m a -> m (ProgramViewT instr m a)
viewT (Lift m)                = m >>= return . Return
viewT (Lift m       `Bind` g) = m >>= viewT . g
viewT ((m `Bind` g) `Bind` h) = viewT (m `Bind` (\x -> g x `Bind` h))
viewT (Instr i      `Bind` g) = return (i :>>= g)
viewT (Instr i)               = return (i :>>= return)

-- | View function for inspecting the first instruction
view :: HFunctor instr => Program instr a -> ProgramView instr a
view = runIdentity . viewT

-- | Turn a 'ProgramViewT' back to a 'Program'
unview :: Monad m => ProgramViewT instr m a -> ProgramT instr m a
unview (Return a) = return a
unview (i :>>= k) = singleton i >>= k



--------------------------------------------------------------------------------
-- * Instructions parameterized on expression language
--------------------------------------------------------------------------------

-- | Extract the expression type from an instruction set
--
-- 'IExp' is needed to avoid types like
-- @(`SomeInstr` exp `:<:` i) => `Program` i ()@. Here it is not possible to
-- constrain @exp@ by constraining @i@, so the instance search will always fail.
-- Functions like 'injE' solve this by using 'IExp' to determine @exp@ from @i@.
-- For this to work, one must use an instruction set @i@ that has an instance of
-- 'IExp'.
--
-- It is common for all instructions in a sum (using ':+:') to use the same
-- expression type. For this common case, it is enough to get the expression
-- type from the first summand. This can be achieved by giving two  'IExp'
-- instances for each instruction:
--
-- @
-- type instance `IExp` (SomeInstr exp)       = exp
-- type instance `IExp` (SomeInstr exp `:+:` i) = exp
-- @
type family IExp (i :: (* -> *) -> * -> *) :: * -> *

-- | Inject an instruction that is parameterized by an expression type
injE :: (i (IExp instr) :<: instr) => i (IExp instr) m a -> instr m a
injE = inj

-- | Project an instruction that is parameterized by an expression type
prjE :: (i (IExp instr) :<: instr) => instr m a -> Maybe (i (IExp instr) m a)
prjE = prj

-- | Create a program from an instruction that is parameterized by an expression type
singleE :: (i (IExp instr) :<: instr) => i (IExp instr) (ProgramT instr m) a -> ProgramT instr m a
singleE = singleton . inj

