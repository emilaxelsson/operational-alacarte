{-# LANGUAGE CPP #-}

-- | = Introduction
--
-- This module gives an alternative to the Operational package \[1\], in which
-- instructions can be higher-order functors, parameterized on the program monad
-- that they are part of. This makes it possible to define instruction sets
-- compositionally using ':+:'. In the normal Operational, this could be done
-- for simple instructions, but here it can be done even for \"control
-- instructions\" -- instructions that take programs as arguments.
--
-- For general information about the ideas behind this module, see the
-- Operational package \[1\].
--
-- \[1\] <http://hackage.haskell.org/package/operational>
--
-- = Example
--
-- (Full code found in
-- <https://github.com/emilaxelsson/operational-alacarte/blob/master/examples/Simple.hs>.)
--
-- An \"if\" instruction can be defined as follows:
--
-- @
-- data If fs a where
--   If :: Exp `Bool` -> prog a -> prog a -> If (`Param1` prog) a
-- @
--
-- Note the use of the type parameter @prog@ to refer to sub-programs. (@Exp@ is
-- some type representing pure expressions.)
--
-- The type @(`Param1` prog)@ can be seen as a type-level list with one element
-- @prog@. (See "Data.ALaCarte" for more details on parameter lists.)
--
-- We can now make program types that combine several instructions; e.g.:
--
-- @type MyProgram = `Program` (If `:+:` Loop `:+:` ...) `Param0`@
--
-- 'Program' is a recursive type that sets the type of the sub-programs of @If@
-- (and @Loop@, etc.) to @MyProgram@. With the original Operational package, we
-- would have to hard-code a specific type for the sub-programs of @If@ (or make
-- @MyProgram@ a recursive newtype, as noted by the author of Operational).
--
-- Interpretation of 'Program' in a monad @m@ can be done using
--
-- @`interpret` :: (`Interp` i m fs, `HFunctor` i, `Monad` m) => `Program` i fs a -> m a@
--
-- In order to use this function, @If@ needs to be an instance of 'Interp' and
-- 'HFunctor'. The 'HFunctor' instance is straightforward:
--
-- @
-- instance `HFunctor` If where
--   `hfmap` f (If c thn els) = If c (f thn) (f els)
-- @
--
-- The 'Interp' type class is parameterized both on the instruction type and the
-- destination monad. For example, interpretation of @If@ in the 'IO' monad
-- might look as follows:
--
-- @
-- instance `Interp` If `IO` fs where
--   `interp` (If c thn els) = if eval c then thn else els
-- @
--
-- (Here @eval@ is the evaluator for the expression languauge @Exp@.)
--
-- The 'Interp' class distributes over ':+:' which means that it is possible to
-- interpret any expression type @(I1 `:+:` I2 `:+:` I3 `:+:` ...)@ to 'IO', as
-- long as the individual instructions (@I1@, @I2@, etc.) have 'Interp'
-- instances for 'IO'.
--
-- = Bi-functorial instructions
--
-- The type @(`Param1` prog)@ in the result of @If@ above says that the
-- instruction has one sub-structure whose type is @prog@. The advanced example
-- <https://github.com/emilaxelsson/operational-alacarte/blob/master/examples/Advanced.hs>
-- shows a version of @If@ that has two parameters:
--
-- @
--   If :: exp `Bool` -> prog a -> prog a -> If (`Param2` prog exp) a
-- @
--
-- @prog@ represents sub-programs and @exp@ represents expressions (@Exp Bool@
-- has been replaced with @exp Bool@).
--
-- This new @If@ instruction is a higher-order /bi-functor/ (see 'HBifunctor').
--
-- The advantage of parameterizing instructions on expressions is that it lets
-- us define generic functions, such as `interpretBi`, which decouple the
-- interpretation of instructions from the interpretation of expressions.
--
-- = Generalized interface
--
-- We have seen two examples of @If@ with a parameter list of one and two
-- arguments respectively (@(`Param1` prog)@ and @(`Param2` prog exp)@). There
-- is nothing stopping us from having instructions with more parameters. For
-- example, we could make a version of @If@ that takes an extra type class
-- constraint @pred@ as parameter:
--
-- @
--   If :: pred a => exp `Bool` -> prog a -> prog a -> If (`Param3` prog exp pred) a
-- @
--
-- (See the documentation to "Data.ALaCarte" regarding why it is a good idea to
-- make @pred@ part of the parameter list rather than just making it a separate
-- parameter.)
--
-- In fact, it is possible to have arbitrarily many parameters to instructions
-- (but the type synonyms for parameter lists stop at 'Param4').
--
-- The functions and types in this module (and "Data.ALaCarte") are designed to
-- be generic in the sense that things that work for parameter lists of /N/
-- elements also work for parameter lists of more elements. For example, the
-- function 'interpret' mentioned above requires the instruction @i@ to be a
-- higher-order functor, but it also works for high-order bi-functors, and for
-- the last version of @If@ that has an additional parameter @pred@.
--
-- = Typical use
--
-- Here we give specialized type signatures for a selection of functions for
-- different uses of the general interface.
--
-- .
--
-- __Functorial instructions with no extra parameters__
--
-- This scenario is used in <https://github.com/emilaxelsson/operational-alacarte/blob/master/examples/Simple.hs>.
--
-- @
-- `singleton` :: instr (`Param1` (`ProgramT` instr `Param0` m)) a -> `ProgramT` instr `Param0` m a
--
-- `interpretWithMonad`
--     :: (`HFunctor` instr, `Monad` m)
--     => (forall b . instr (`Param1` m) b -> m b)
--     -> `Program` instr `Param0` a -> m a
--
-- `interpret`
--     :: (`Interp` i m `Param0`, `HFunctor` i, `Monad` m)
--     => `Program` i `Param0` a -> m a
-- @
--
-- .
--
-- __Functorial instructions with extra parameter__
--
-- Like the previous scenario but with an extra parameter @p@ (poly-kinded) that instructions can use for anything.
--
-- @
-- `singleton` :: instr (`Param2` (`ProgramT` instr (`Param1` p) m) p) a -> `ProgramT` instr (`Param1` p) m a
--
-- `interpretWithMonad`
--     :: (`HFunctor` instr, `Monad` m)
--     => (forall b . instr (`Param2` m p) b -> m b)
--     -> `Program` instr (`Param1` p) a -> m a
--
-- `interpret`
--     :: (`Interp` i m (`Param1` p), `HFunctor` i, `Monad` m)
--     => `Program` i (`Param1` p) a -> m a
-- @
--
-- .
--
-- __Bi-functorial instructions with no extra parameters__
--
-- This scenario is used in <https://github.com/emilaxelsson/operational-alacarte/blob/master/examples/Advanced.hs>.
--
-- The parameter @exp@ is an extra interpreted structure that e.g. can represent expressions.
--
-- @
-- `singleton` :: instr (`Param2` (`ProgramT` instr (`Param1` exp) m) exp) a -> `ProgramT` instr (`Param1` exp) m a
--
-- `interpretWithMonadBi`
--     :: (`HBifunctor` instr, `Functor` m, `Monad` m)
--     => (forall b . exp b -> m b)
--     -> (forall b . instr (`Param2` m m) b -> m b)
--     -> `Program` instr (`Param1` exp) a -> m a
--
-- `interpret`
--     :: (`InterpBi` i m `Param0`, `HBifunctor` i, `Functor` m, `Monad` m)
--     => (forall b . exp b -> m b) -> `Program` i (`Param1` exp) a -> m a
-- @
--
-- .
--
-- __Bi-functorial instructions with extra parameter__
--
-- Like the previous scenario but with an extra parameter @p@ (poly-kinded) that instructions can use for anything.
--
-- @
-- `singleton` :: instr (`Param3` (`ProgramT` instr (`Param2` exp p) m) exp p) a -> `ProgramT` instr (`Param2` exp p) m a
--
-- `interpretWithMonadBi`
--     :: (`HBifunctor` instr, `Functor` m, `Monad` m)
--     => (forall b . exp b -> m b)
--     -> (forall b . instr (`Param3` m m p) b -> m b)
--     -> `Program` instr (`Param2` exp p) a -> m a
--
-- `interpret`
--     :: (`InterpBi` i m (`Param1` p), `HBifunctor` i, `Functor` m, `Monad` m)
--     => (forall b . exp b -> m b) -> `Program` i (`Param2` exp p) a -> m a
-- @

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
    , ProgViewT
    , ProgView
    , viewT
    , view
    , unview
      -- * Bi-functorial instructions
    , interpretWithMonadBiT
    , interpretWithMonadBi
    , InterpBi (..)
    , interpretBiT
    , interpretBi
    , Reexpressible (..)
    , reexpress
    , reexpressEnv
    ) where



#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Reader
import Data.Typeable

import Data.ALaCarte



--------------------------------------------------------------------------------
-- * Program monad
--------------------------------------------------------------------------------

-- | Representation of programs parameterized by the primitive instructions
-- (transformer version)
data ProgramT instr fs m a
  where
    Lift  :: m a -> ProgramT instr fs m a
    Bind  :: ProgramT instr fs m a ->
               (a -> ProgramT instr fs m b) -> ProgramT instr fs m b
    Instr :: instr '(ProgramT instr fs m, fs) a -> ProgramT instr fs m a
#if  __GLASGOW_HASKELL__>=708
  deriving Typeable
#endif

-- | Representation of programs parameterized by the primitive instructions
type Program instr fs = ProgramT instr fs Identity

instance Monad m => Functor (ProgramT instr fs m)
  where
    fmap = liftM

instance Monad m => Applicative (ProgramT instr fs m)
  where
    pure  = Lift . pure
    (<*>) = ap

instance Monad m => Monad (ProgramT instr fs m)
  where
    return = pure
    (>>=)  = Bind

instance MonadTrans (ProgramT instr fs)
  where
    lift = Lift

-- | Make a program from a single instruction
singleton :: instr '(ProgramT instr fs m, fs) a -> ProgramT instr fs m a
singleton = Instr

-- | Make a program from a single instruction
singleInj :: (i :<: instr) =>
    i '(ProgramT instr fs m, fs) a -> ProgramT instr fs m a
singleInj = Instr . inj



--------------------------------------------------------------------------------
-- * Interpretation
--------------------------------------------------------------------------------

-- | Lift a program to a program transformer
liftProgram :: forall instr fs m a . (HFunctor instr, Monad m)
    => Program instr fs a  -- ^ Program to lift
    -> ProgramT instr fs m a
liftProgram = go
  where
    go :: Program instr fs b -> ProgramT instr fs m b
    go (Lift a)   = Lift $ return $ runIdentity a
    go (Bind p k) = Bind (go p) (go . k)
    go (Instr i)  = Instr $ hfmap go i

-- | Interpret a program in a monad
interpretWithMonadT :: forall instr fs m n a . (HFunctor instr, Monad m)
    => (forall b . instr '(m,fs) b -> m b)  -- ^ Interpretation of instructions
    -> (forall b . n b -> m b)              -- ^ Interpretation of the underlying monad
    -> ProgramT instr fs n a -> m a
interpretWithMonadT inti intn = go
  where
    go :: ProgramT instr fs n b -> m b
    go (Lift a)   = intn a
    go (Bind p k) = go p >>= (go . k)
    go (Instr i)  = inti $ hfmap go i

-- | Interpret a program in a monad
interpretWithMonad :: (HFunctor instr, Monad m)
    => (forall b . instr '(m,fs) b -> m b)  -- ^ Interpretation of instructions
    -> Program instr fs a -> m a
interpretWithMonad interp = interpretWithMonadT interp (return . runIdentity)

-- | @`Interp` instr m fs@ represents the fact that @instr@ can be interpreted
-- in the monad @m@
class Interp instr m fs
  where
    -- | Interpret an instruction in a monad
    interp :: instr '(m,fs) a -> m a

instance (Interp i1 m fs, Interp i2 m fs) => Interp (i1 :+: i2) m fs
  where
    interp (Inl i) = interp i
    interp (Inr i) = interp i

-- | Interpret a program in a monad. The interpretation of instructions is
-- provided by the 'Interp' class.
interpretT :: (Interp i m fs, HFunctor i, Monad m)
    => (forall b . n b -> m b)  -- ^ Interpretation of the underlying monad
    -> ProgramT i fs n a -> m a
interpretT = interpretWithMonadT interp

-- | Interpret a program in a monad. The interpretation of instructions is
-- provided by the 'Interp' class.
interpret :: (Interp i m fs, HFunctor i, Monad m) => Program i fs a -> m a
interpret = interpretWithMonad interp

-- | View type for inspecting the first instruction
data ProgramViewT instr fs m a
  where
    Return :: a -> ProgramViewT instr fs m a
    (:>>=)
        :: instr '(ProgramT instr fs m, fs) b
        -> (b -> ProgramT instr fs m a)
        -> ProgramViewT instr fs m a

-- | View type for inspecting the first instruction
type ProgramView instr fs = ProgramViewT instr fs Identity

type ProgViewT instr m = ProgramViewT instr '() m
type ProgView instr    = ProgramView instr '()

-- | View function for inspecting the first instruction
viewT :: Monad m => ProgramT instr fs m a -> m (ProgramViewT instr fs m a)
viewT (Lift m)                = m >>= return . Return
viewT (Lift m       `Bind` g) = m >>= viewT . g
viewT ((m `Bind` g) `Bind` h) = viewT (m `Bind` (\x -> g x `Bind` h))
viewT (Instr i      `Bind` g) = return (i :>>= g)
viewT (Instr i)               = return (i :>>= return)

-- | View function for inspecting the first instruction
view :: HFunctor instr => Program instr fs a -> ProgramView instr fs a
view = runIdentity . viewT

-- | Turn a 'ProgramViewT' back to a 'Program'
unview :: Monad m => ProgramViewT instr fs m a -> ProgramT instr fs m a
unview (Return a) = return a
unview (i :>>= k) = singleton i >>= k



--------------------------------------------------------------------------------
-- * Bi-functorial instructions
--------------------------------------------------------------------------------

-- | Bi-functorial version of 'interpretWithMonadT'
--
-- Bi-functorial instructions are of the form @instr '(prog, '(exp, ...)) a@,
-- where @prog@ is a representation of sub-programs, and @exp@ is a
-- representation of some other sub-structure, e.g. expressions.
-- 'interpretWithMonadBiT' allows interpreting both these kinds of
-- sub-structures in a generic way.
interpretWithMonadBiT :: (HBifunctor instr, Functor m, Monad m, Monad n)
    => (forall b . exp b -> m b)                 -- ^ Interpretation of the @exp@ sub-structure
    -> (forall b . instr '(m,'(m,fs)) b -> m b)  -- ^ Interpretation of instructions
    -> (forall b . n b -> m b)                   -- ^ Interpretation of the underlying monad
    -> ProgramT instr '(exp,fs) n a -> m a
interpretWithMonadBiT inte inti intn = interpretWithMonadT
    (\i -> inti $ hbimap id inte i)
    intn

-- | Bi-functorial version of 'interpretWithMonad'
--
-- See explanation of 'interpretWithMonadBiT'.
interpretWithMonadBi :: (HBifunctor instr, Functor m, Monad m)
    => (forall b . exp b -> m b)                 -- ^ Interpretation of the @exp@ sub-structure
    -> (forall b . instr '(m,'(m,fs)) b -> m b)  -- ^ Interpretation of instructions
    -> Program instr '(exp,fs) a -> m a
interpretWithMonadBi inte inti = interpretWithMonadBiT inte inti
    (return . runIdentity)

-- | @`InterpBi` instr m fs@ represents the fact that the bi-functorial
-- instruction @instr@ can be interpreted in the monad @m@
class InterpBi instr m fs
  where
    -- | Interpret a bi-functorial instruction in a monad
    interpBi :: instr '(m,'(m,fs)) a -> m a

instance (InterpBi i1 m fs, InterpBi i2 m fs) => InterpBi (i1 :+: i2) m fs
  where
    interpBi (Inl i) = interpBi i
    interpBi (Inr i) = interpBi i

-- | Interpret a program in a monad. The interpretation of instructions is
-- provided by the 'InterpBi' class.
interpretBiT :: (InterpBi i m fs, HBifunctor i, Functor m, Monad m, Monad n)
    => (forall b . exp b -> m b)  -- ^ Interpretation of the @exp@ sub-structure
    -> (forall b . n b -> m b)    -- ^ Interpretation of the underlying monad
    -> ProgramT i '(exp,fs) n a -> m a
interpretBiT inte = interpretWithMonadBiT inte interpBi
  -- The reason for only getting the interpretation of instructions from a class
  -- (and not the interpretation of `exp`), is that `interpBi` is constructed
  -- automatically for instructions built using `:+:`. It would be quite
  -- cumbersome to construct this function by hand.

-- | Interpret a program in a monad. The interpretation of instructions is
-- provided by the 'InterpBi' class.
interpretBi :: (InterpBi i m fs, HBifunctor i, Functor m, Monad m)
    => (forall b . exp b -> m b)  -- ^ Interpretation of the @exp@ sub-structure
    -> Program i '(exp,fs) a -> m a
interpretBi inte = interpretWithMonadBi inte interpBi

-- | Reexpressible types
--
-- @i@ is a bi-functorial instruction where, in the type @i '(p,'(e1,...)) a@,
-- sub-structure @e1@ can be converted to a different sub-structure @e2@.
--
-- @e1@ and @e2@ typically represent expressions; hence the name
-- \"reexpressible\".
class HBifunctor i => Reexpressible i instr env
  where
    -- | Rewrite an instruction changing its \"expression\" sub-structure
    --
    -- As an example of how to define this function, take the following
    -- instruction that just puts a tag on a sub-program:
    --
    -- @
    -- data Tag fs a
    --   where
    --     Tag :: `String` -> prog () -> Tag (`Param2` prog exp) ()
    -- @
    --
    -- To define `reexpressInstrEnv` we have to use a combination of `ReaderT`
    -- and `runReaderT`:
    --
    -- @
    -- instance (Tag `:<:` instr) => `Reexpressible` Tag instr
    --   where
    --     `reexpressInstrEnv` reexp (Tag tag prog) = `ReaderT` `$` \env ->
    --         `singleInj` `$` Tag tag (`flip` `runReaderT` env prog)
    -- @
    reexpressInstrEnv :: Monad m
        => ( forall b .
               exp1 b -> ReaderT env (ProgramT instr '(exp2,fs) m) (exp2 b)
           )
             -- ^ Conversion of the \"expression\" sub-structure
        -> i '(ReaderT env (ProgramT instr '(exp2,fs) m), '(exp1, fs)) a
        -> ReaderT env (ProgramT instr '(exp2,fs) m) a
      -- The reason for only allowing `ReaderT` is that for instructions that
      -- have sub-programs, this seems to be the only possible transformer for
      -- which `reexpressInstrEnv` can be defined (among common monads). E.g.
      -- the above trick with `runReaderT` doesn't work for `StateT`.

-- | Rewrite an instruction changing its \"expression\" sub-structure
reexpressInstr :: (Reexpressible i instr (), Monad m)
    => (forall b . exp1 b -> ProgramT instr '(exp2,fs) m (exp2 b))
         -- ^ Conversion of the \"expression\" sub-structure
    -> i '(ProgramT instr '(exp2,fs) m, '(exp1, fs)) a
    -> ProgramT instr '(exp2,fs) m a
reexpressInstr reexp
    = flip runReaderT ()
    . reexpressInstrEnv (lift . reexp)
    . hbimap lift id

instance (Reexpressible i1 instr env, Reexpressible i2 instr env) =>
    Reexpressible (i1 :+: i2) instr env
  where
    reexpressInstrEnv reexp (Inl i) = reexpressInstrEnv reexp i
    reexpressInstrEnv reexp (Inr i) = reexpressInstrEnv reexp i

-- | Rewrite a program changing its expression type (assuming that the second
-- sub-structure of the instruction type represents expressions)
--
-- Conversion of expressions is done in the target monad, so pure expressions
-- are allowed to expand to monadic code. This can be used e.g. to \"compile\"
-- complex expressions into simple expressions with supporting monadic code.
reexpress :: (Reexpressible instr1 instr2 (), Monad m)
    => (forall b . exp1 b -> ProgramT instr2 '(exp2,fs) m (exp2 b))
         -- ^ Conversion of expressions
    -> ProgramT instr1 '(exp1,fs) m a -> ProgramT instr2 '(exp2,fs) m a
reexpress reexp p = interpretWithMonadT (reexpressInstr reexp) lift p

-- | Rewrite a program changing its expression type (assuming that the second
-- sub-structure of the instruction type represents expressions)
--
-- Conversion of expressions is done in the target monad, so pure expressions
-- are allowed to expand to monadic code. This can be used e.g. to \"compile\"
-- complex expressions into simple expressions with supporting monadic code.
reexpressEnv :: (Reexpressible instr1 instr2 env, Monad m)
    => ( forall b .
            exp1 b -> ReaderT env (ProgramT instr2 '(exp2,fs) m) (exp2 b)
       )
         -- ^ Conversion of expressions
    -> ProgramT instr1 '(exp1,fs) m a
    -> ReaderT env (ProgramT instr2 '(exp2,fs) m) a
reexpressEnv reexp p =
    interpretWithMonadT (reexpressInstrEnv reexp) (lift . lift) p

