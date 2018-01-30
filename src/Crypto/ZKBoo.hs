{-# LANGUAGE BangPatterns #-}
module Crypto.ZKBoo
  ( GateId(..)
  , Expr(..)
  , Circuit(..)
  , View(..)
  , decomposeEval
  , eval
  , output
  ) where

import           Control.Monad
import           Crypto.Random
import           Data.List (foldl')
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import           Crypto.ZKBoo.Util


-- Inputs are also represented as GateIds with the difference being that they are never assigned
newtype GateId = GateId Int
  deriving (Eq, Ord, Show)

data Expr f =
    AddConst GateId f
  | MultConst GateId f
  | Add GateId GateId
  | Mult GateId GateId
  deriving (Show)

data Circuit f = Circuit
  { inputs :: [GateId]
  , outputs :: [GateId]
  -- | We assume that
  -- * assignments are toplogically sorted
  -- * there are no assignments for the inputs
  -- * each gate is only assigned once
  -- * all output gates have an assignment
  , assignments :: [(GateId, Expr f)] -- We assume that assignments
  } deriving (Show)

-- | A view consists of a mapping from 'GateId's to values in the
-- ring @f@. Initially, the mapping only contains entries for the input
-- values.
data View f gen = View
  { values :: Map GateId f
  , originalGen :: gen -- ^ We save the originalGen for convenience
  , gen :: gen
  }

insert :: GateId -> f -> View f gen -> View f gen
insert i v (View m g g') = View (Map.insert i v m) g g'

(!) :: View f gen -> GateId -> f
(!) (View m _ _) i = m Map.! i

getRandomElement :: (DRG gen, RandomElement f) => View f gen -> (f, View f gen)
getRandomElement (View vs og g) =
  case withDRG g randomElement of
    (v, g') -> (v, View vs og g')

f :: (DRG gen, Num f, RandomElement f) => GateId -> Expr f -> View f gen -> View f gen -> View f gen
f i (AddConst a alpha)  wi _   = insert i (wi ! a + alpha)  wi
f i (MultConst a alpha) wi _   = insert i (wi ! a * alpha)  wi
f i (Add a b)           wi _   = insert i (wi ! a + wi ! b) wi
f i (Mult a b)          wi wi1 =
  case (getRandomElement wi, getRandomElement wi1) of
    ((ri, wi'), (ri1, wi1')) ->
      let v = wi'  ! a * wi'  ! b +
              wi1' ! a * wi'  ! b +
              wi'  ! a * wi1' ! b +
              ri - ri1
      in insert i v wi'

step :: (DRG gen, Num f, RandomElement f)
     => GateId -> Expr f -> View f gen -> View f gen -> View f gen -> (View f gen, View f gen, View f gen)
step i gate w0 w1 w2 =
  let w0' = f i gate w0 w1
      w1' = f i gate w1 w2
      w2' = f i gate w2 w0
  in (w0', w1', w2')

output :: Num f => [GateId] -> View f gen -> View f gen -> View f gen -> [f]
output os w0 w1 w2 =
  let o1 = map (w0 !) os
      o2 = map (w1 !) os
      o3 = map (w2 !) os
  in zipWith3 (\x y z -> x + y + z) o1 o2 o3

eval :: Num f => Circuit f -> [f] -> [f]
eval circuit inputValues =
  let m = Map.fromList (zip (inputs circuit) inputValues)
      mFinal = foldl' step' m (assignments circuit)
  in map (\g -> mFinal Map.! g) (outputs circuit)
  where step' :: Num f => Map GateId f -> (GateId, Expr f) -> Map GateId f
        step' m' (i, g) = case g of
          AddConst a alpha  -> Map.insert i (m' Map.! a + alpha)      m'
          MultConst a alpha -> Map.insert i (m' Map.! a * alpha)      m'
          Add a b           -> Map.insert i (m' Map.! a + m' Map.! b) m'
          Mult a b          -> Map.insert i (m' Map.! a * m' Map.! b) m'

decomposeEval :: (DRG gen, Num f, RandomElement f) => Circuit f -> [f] -> gen -> gen -> gen -> (View f gen, View f gen, View f gen)
decomposeEval circuit inputValues g0 g1 g2 =
  let (i0, g0') = withDRG g0 randomInputs
      (i1, g1') = withDRG g1 randomInputs
      i2 = zipWith3 (\x y z -> x - y - z) inputValues i0 i1
      v0 = View (Map.fromList (zip (inputs circuit) i0)) g0' g0'
      v1 = View (Map.fromList (zip (inputs circuit) i1)) g1' g1'
      v2 = View (Map.fromList (zip (inputs circuit) i2)) g2 g2
  in foldl' (\(!v0', !v1', !v2') (i, g) -> step i g v0' v1' v2') (v0, v1, v2) (assignments circuit)
  where randomInputs :: (MonadRandom m, RandomElement f) => m [f]
        randomInputs = replicateM (length (inputs circuit)) randomElement
