{-# LANGUAGE CPP #-}

#ifndef MIN_VERSION_GLASGOW_HASKELL
#define MIN_VERSION_GLASGOW_HASKELL(a,b,c,d) 0
#endif
  -- MIN_VERSION_GLASGOW_HASKELL was introduced in GHC 7.10

#if MIN_VERSION_GLASGOW_HASKELL(7,10,0,0)
#else
{-# LANGUAGE OverlappingInstances #-}
#endif

-- | This module provides a generalized implementation of data types à la carte
-- [1]. It supports (higher-order) functors with 0 or more functorial parameters
-- and additional non-functorial parameters, all with a uniform interface.
--
-- \[1\] W. Swierstra. Data Types à la Carte.
--       /Journal of Functional Programming/, 18(4):423-436, 2008,
--       <http://dx.doi.org/10.1017/S0956796808006758>.
--
-- (This module is preferably used with the GHC extensions @DataKinds@ and
-- @PolyKinds@.)
--
-- = Usage
--
-- Compared to traditional data types à la carte, an extra poly-kinded parameter
-- has been added to ':+:' and to the parameters of ':<:'. Standard data types à
-- la carte is obtained by setting this parameter to @()@. That gives us the
-- following type for 'Inl':
--
-- @`Inl` :: h1 () a -> (h1 `:+:` h2) () a@
--
-- Here, @h1 ()@ and @(h1 `:+:` h2) ()@ are functors.
--
-- By setting the extra parameter to a functor @f :: * -> *@, we obtain this
-- type:
--
-- @`Inl` :: h1 f a -> (h1 `:+:` h2) f a@
--
-- This makes @h1@ and @(h1 `:+:` h2)@ higher-order functors.
--
-- Finally, by setting the parameter to a type-level pair of functors
-- @'(f,g) :: (* -> *, * -> *)@, we obtain this type:
--
-- @`Inl` :: h1 '(f,g) a -> (h1 `:+:` h2) '(f,g) a@
--
-- This makes @h1@ and @(h1 `:+:` h2)@ higher-order bi-functors.
--
-- Alternatively, we can represent all three cases above using heterogeneous
-- lists of functors constructed using @'(,)@ and terminated by @()@:
--
-- @
-- `Inl` :: h1 ()           a -> (h1 `:+:` h2) ()           a  -- functor
-- `Inl` :: h1 '(f,())      a -> (h1 `:+:` h2) '(f,())      a  -- higher-order functor
-- `Inl` :: h1 '(f,'(g,())) a -> (h1 `:+:` h2) '(f,'(g,())) a  -- higher-order bi-functor
-- @
--
-- This view is taken by the classes 'HFunctor' and 'HBifunctor'. An 'HFunctor'
-- takes a parameter of kind @(* -> *, k)@; i.e. it has /at least/ one
-- functorial parameter. A 'HBiFunctor' takes a parameter of kind
-- @(* -> *, (* -> *, k))@; i.e. it has /at least/ two functorial parameters.
--
-- = Aliases for parameter lists
--
-- To avoid ugly types such as @'(f,'(g,()))@, this module exports the synonyms
-- 'Param0', 'Param1', 'Param2', etc. for parameter lists up to size 4. These
-- synonyms allow the module to be used without the @DataKinds@ extension.
--
-- = Extra type parameters
--
-- Recall that an 'HFunctor' takes a parameter of kind @(* -> *, k)@, and an
-- 'HBifunctor' takes a parameter of kind @(* -> *, (* -> *, k))@. Since @k@ is
-- polymorphic, it means that it is possible to add extra parameters in place of
-- @k@.
--
-- For example, a user can define the following type representing addition in
-- some language:
--
-- @
-- data Add fs a where
--   Add :: (`Num` a, pred a) => f a -> f a -> Add (`Param2` f pred) a
--
-- instance `HFunctor` Add where
--   `hfmap` f (Add a b) = Add (f a) (f b)
-- @
--
-- Here, @Add@ has a functorial parameter @f@, and an extra non-functorial
-- parameter @pred@ that provides a constraint for the type @a@.
--
-- An obvious alternative would have been to just make @pred@ a separate
-- parameter to @Add@:
--
-- @
-- data Add pred fs a where
--   Add :: (`Num` a, pred a) => f a -> f a -> Add pred (`Param1` f) a
--
-- instance `HFunctor` (Add pred) where
--   `hfmap` f (Add a b) = Add (f a) (f b)
-- @
--
-- However, this has the disadvantage of being hard to use together with the
-- ':<:' class. For example, we might want to define the following \"smart
-- constructor\" for @Add@:
--
-- @
-- mkAdd :: (`Num` a, pred a, Add pred `:<:` h) => f a -> f a -> h (`Param1` f) a
-- mkAdd a b = `inj` (Add a b)
-- @
--
-- Unfortunately, the above type is ambiguous, because @pred@ is completely
-- free. Assuming that @h@ is a type of the form @(... `:+:` Add `Show` `:+:` ...)@,
-- we would like to infer @(pred ~ `Show`)@, but this would require extra
-- machinery, such as a type family that computes @pred@ from @h@.
--
-- By putting @pred@ in the parameter list, we avoid the above problem. We also
-- get the advantage that the same @pred@ parameter is distributed to all types
-- in a sum constructed using ':+:'. This makes it easier to, for example,
-- change the @pred@ parameter uniformly throughout an expression.

module Data.ALaCarte where



-- | Coproducts
data (h1 :+: h2) fs a
    = Inl (h1 fs a)
    | Inr (h2 fs a)
#if  __GLASGOW_HASKELL__>=708
  deriving (Functor)
#endif

infixr :+:

-- | A constraint @f `:<:` g@ expresses that the signature @f@ is subsumed by
-- @g@, i.e. @f@ can be used to construct elements in @g@.
class sub :<: sup
  where
    inj :: sub fs a -> sup fs a
    prj :: sup fs a -> Maybe (sub fs a)

instance {-# OVERLAPPING #-} (f :<: f)
  where
    inj = id
    prj = Just

instance {-# OVERLAPPING #-} (f :<: (f :+: g))
  where
    inj = Inl
    prj (Inl f) = Just f
    prj _       = Nothing

instance {-# OVERLAPPING #-} (f :<: h) => (f :<: (g :+: h))
  where
    inj = Inr . inj
    prj (Inr h) = prj h
    prj _       = Nothing

-- | Higher-order functors
class HFunctor h
  where
    -- | Higher-order 'fmap'
    hfmap :: (forall b . f b -> g b) -> h '(f,fs) a -> h '(g,fs) a

instance (HFunctor h1, HFunctor h2) => HFunctor (h1 :+: h2)
  where
    hfmap f (Inl i) = Inl (hfmap f i)
    hfmap f (Inr i) = Inr (hfmap f i)

-- | Higher-order bi-functors
class HFunctor h => HBifunctor h
  where
    -- | Higher-order \"bimap\"
    hbimap :: (Functor f, Functor g)
        => (forall b . f b -> g b)
        -> (forall b . i b -> j b)
        -> h '(f,'(i,fs)) a
        -> h '(g,'(j,fs)) a

instance (HBifunctor h1, HBifunctor h2) => HBifunctor (h1 :+: h2)
  where
    hbimap f g (Inl i) = Inl (hbimap f g i)
    hbimap f g (Inr i) = Inr (hbimap f g i)



--------------------------------------------------------------------------------
-- * Parameter lists
--------------------------------------------------------------------------------

-- | Empty parameter list
type Param0 = ()

-- | Singleton parameter list
type Param1 a = '(a,Param0)

-- | Two-element parameter list
type Param2 a b = '(a, Param1 b)

-- | Three-element parameter list
type Param3 a b c = '(a, Param2 b c)

-- | Four-element parameter list
type Param4 a b c d = '(a, Param3 b c d)

