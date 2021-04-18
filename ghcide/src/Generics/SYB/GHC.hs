{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE RankNTypes          #-}

-- | Custom SYB traversals explicitly designed for operating over the GHC AST.
{-# LANGUAGE DeriveDataTypeable #-}
module Generics.SYB.GHC
    ( genericIsSubspan,
      mkBindListT,
      everywhereM',
      smallestM,
      largestM,
      mkQ1,
      genericDefinitelyNotIsSubspan,
    ) where

import           Control.Monad
import           Data.Bool
import           Data.Functor.Compose (Compose(Compose))
import           Data.Monoid (Any(Any))
import           Data.Semigroup (Min(Min))
import           Development.IDE.GHC.Compat
import           Development.Shake.Classes
import qualified GHC.Exts as GHC
import           Generics.SYB hiding (typeRep)
import           Type.Reflection
import           Unsafe.Coerce (unsafeCoerce)


data QueryResult
  = Success
  | Failure
  | Unknown
  | Pruned
  deriving stock (Eq, Ord, Show, Enum, Bounded)
  deriving (Semigroup, Monoid) via Min QueryResult


-- | Like 'mkQ', but allows for polymorphic instantiation of its specific case.
-- This instantation matches whenever the dynamic value has the same
-- constructor as the proxy @f ()@ value.
mkQ1 :: forall a r f
      . (Data a, Data (f ()))
     => f ()                  -- ^ Polymorphic constructor to match on
     -> r                     -- ^ Default value
     -> (forall b. f b -> r)  -- ^ Polymorphic match
     -> a
     -> r
mkQ1 proxy r br a =
    case l_con == a_con && sameTypeModuloLastApp @a @(f ()) of
      -- We have proven that the two values share the same constructor, and
      -- that they have the same type if you ignore the final application.
      -- Therefore, it is safe to coerce @a@ to @f b@, since @br@ is universal
      -- over @b@ and can't inspect it.
      True  -> br $ unsafeCoerce @_ @(f GHC.Any) a
      False -> r
  where
    l_con = toConstr proxy
    a_con = toConstr a

-- | Given @a ~ f1 a1@ and @b ~ f2 b2@, returns true if @f1 ~ f2@.
sameTypeModuloLastApp :: forall a b. (Typeable a, Typeable b) => Bool
sameTypeModuloLastApp =
  let tyrep1 = typeRep @a
      tyrep2 = typeRep @b
   in case (tyrep1 , tyrep2) of
        (App a _, App b _) ->
          case eqTypeRep a b of
            Just HRefl -> True
            Nothing    -> False
        _ -> False


-- | A generic query intended to be used for calling 'smallestM' and
-- 'largestM'. If the current node is a 'Located', returns whether or not the
-- given 'SrcSpan' is a subspan. For all other nodes, returns 'Nothing', which
-- indicates uncertainty. The search strategy in 'smallestM' et al. will
-- continue searching uncertain nodes.
genericIsSubspan ::
    forall ast.
    Typeable ast =>
    -- | The type of nodes we'd like to consider.
    Proxy (Located ast) ->
    SrcSpan ->
    GenericQ (Maybe Bool)
genericIsSubspan _ dst =
  genericDefinitelyNotIsSubspan dst `extQ` \case
  (L span _ :: Located ast) -> Just $ dst `isSubspanOf` span


-- | Returns 'Just False' if it encounters a 'Located' which doesn't contain
-- the given 'SrcSpan', 'Nothing' otherwise.
genericDefinitelyNotIsSubspan
    :: SrcSpan
    -> GenericQ (Maybe Bool)
genericDefinitelyNotIsSubspan dst = mkQ1 (L noSrcSpan ()) Nothing $ \case
  L span _ -> bool (Just False) Nothing $ dst `isSubspanOf` span


-- | Lift a function that replaces a value with several values into a generic
-- function. The result doesn't perform any searching, so should be driven via
-- 'everywhereM' or friends.
--
-- The 'Int' argument is the index in the list being bound.
mkBindListT :: forall b m. (Data b, Monad m) => (Int -> b -> m [b]) -> GenericM m
mkBindListT f = mkM $ fmap join . traverse (uncurry f) . zip [0..]


-- | Apply a monadic transformation everywhere in a top-down manner.
everywhereM' :: forall m. Monad m => GenericM m -> GenericM m
everywhereM' f = go
    where
        go :: GenericM m
        go = gmapM go <=< f


------------------------------------------------------------------------------
-- Custom SYB machinery
------------------------------------------------------------------------------

-- | Generic monadic transformations that return side-channel data.
type GenericMQ r m = forall a. Data a => a -> m (r, a)

------------------------------------------------------------------------------
-- | Apply the given 'GenericM' at all every node whose children fail the
-- 'GenericQ', but which passes the query itself.
--
-- The query must be a monotonic function when it returns 'Just'. That is, if
-- @s@ is a subtree of @t@, @q t@ should return @Just True@ if @q s@ does. It
-- is the True-to-false edge of the query that triggers the transformation.
--
-- Why is the query a @Maybe Bool@? The GHC AST intersperses 'Located' nodes
-- with data nodes, so for any given node we can only definitely return an
-- answer if it's a 'Located'. See 'genericIsSubspan' for how this parameter is
-- used.
smallestM :: forall m. Monad m => GenericQ (Maybe Bool) -> GenericM m -> GenericM m
smallestM q f = fmap snd . go
  where
    go :: GenericMQ (Maybe Any) m
    go x = do
      case q x of
        Nothing -> gmapMQ go x
        Just True -> do
          it@(r, x') <- gmapMQ go x
          case r of
            Just (Any True) -> pure it
            _ -> fmap (Just $ Any True,) $ f x'
        Just False -> pure (mempty, x)

------------------------------------------------------------------------------
-- | Apply the given 'GenericM' at every node that passes the 'GenericQ', but
-- don't descend into children if the query matches. Because this traversal is
-- root-first, this policy will find the largest subtrees for which the query
-- holds true.
--
-- Why is the query a @Maybe Bool@? The GHC AST intersperses 'Located' nodes
-- with data nodes, so for any given node we can only definitely return an
-- answer if it's a 'Located'. See 'genericIsSubspan' for how this parameter is
-- used.
largestM :: forall m. Monad m => GenericQ (Maybe Bool) -> GenericM m -> GenericM m
largestM q f = go
  where
    go :: GenericM m
    go x = do
      case q x of
        Just True -> f x
        Just False -> pure x
        Nothing -> gmapM go x

newtype MonadicQuery r m a = MonadicQuery
  { runMonadicQuery :: m (r, a)
  }
  deriving stock (Functor)
  deriving Applicative via Compose m ((,) r)


------------------------------------------------------------------------------
-- | Like 'gmapM', but also returns side-channel data.
gmapMQ ::
    forall f r a. (Monoid r, Data a, Applicative f) =>
    (forall d. Data d => d -> f (r, d)) ->
    a ->
    f (r, a)
gmapMQ f = runMonadicQuery . gfoldl k pure
  where
    k :: Data d => MonadicQuery r f (d -> b) -> d -> MonadicQuery r f b
    k c x = c <*> MonadicQuery (f x)


data Test = Test [Int] [Bool]
  deriving Data

