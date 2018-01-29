{-# LANGUAGE BangPatterns #-}
module Crypto.ZKBoo
  (
  ) where

import           Control.Monad
import           Crypto.Random
import           Data.List (foldl')
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import           Crypto.ZKBoo.Util


-- Inputs are also represented as GateIds with the difference being that they are never assigned
newtype GateId = GateId Int
  deriving (Eq, Ord)

data Expr f =
    AddConst GateId f
  | MultConst GateId f
  | Add GateId GateId
  | Mult GateId GateId

data Circuit f = Circuit
  { inputs :: [GateId]
  , outputs :: [GateId]
  -- | We assume that
  -- * assignments are toplogically sorted
  -- * there are no assignments for the inputs
  -- * each gate is only assigned once
  -- * all output gates have an assignment
  , assignments :: [(GateId, Expr f)] -- We assume that assignments
  }

-- | A view consists of a mapping from 'GateId's to values in the
-- ring @f@. Initially, the mapping only contains entries for the input
-- values.
data View f gen = View
  { values :: Map GateId f
  , originalGen :: gen -- ^ We save the originalGen for convenience
  , gen :: gen
  }

insert :: GateId -> f -> View f gen -> View f gen
insert i f (View m g g') = View (Map.insert i f m) g g'

(!) :: View f gen -> GateId -> f
(!) (View m _ _) i = m Map.! i

getRandomElement :: (DRG gen, RandomElement f) => View f gen -> (f, View f gen)
getRandomElement (View vs originalGen gen) =
  case withDRG gen randomElement of
    (f, gen') -> (f, View vs originalGen gen')

f :: (DRG gen, Num f, RandomElement f) => GateId -> Expr f -> View f gen -> View f gen -> (View f gen, View f gen)
f i (AddConst a alpha)  wi wi1 = (insert i (wi ! a + alpha)  wi, wi1)
f i (MultConst a alpha) wi wi1 = (insert i (wi ! a * alpha)  wi, wi1)
f i (Add a b)           wi wi1 = (insert i (wi ! a + wi ! b) wi, wi1)
f i (Mult a b)          wi wi1 =
  case (getRandomElement wi, getRandomElement wi1) of
    ((ri, wi'), (ri1, wi1')) ->
      let v =
            wi'  ! a * wi'  ! b +
            wi1' ! a * wi'  ! b +
            wi'  ! a * wi1' ! b +
            ri - ri1
      in (insert i v wi', wi1')

output :: Num f => [GateId] -> View f gen -> View f gen -> View f gen -> [f]
output outputs w0 w1 w2 =
  let o1 = map (w0 !) outputs
      o2 = map (w1 !) outputs
      o3 = map (w2 !) outputs
  in zipWith3 (\x y z -> x + y + z) o1 o2 o3

step :: (DRG gen, Num f, RandomElement f)
     => GateId -> Expr f -> View f gen -> View f gen -> View f gen -> (View f gen, View f gen, View f gen)
step i gate w0 w1 w2 =
  case f i gate w0 w1 of
    (w0', w1') -> case f i gate w1' w2 of
      (w1'', w2') -> case f i gate w2' w0' of
        (w2'', w0'') -> (w0'', w1'', w2'')

eval :: (DRG gen, Num f, RandomElement f) => Circuit f -> [f] -> gen -> gen -> gen -> (View f gen, View f gen, View f gen)
eval (Circuit inputs outputs assignments) inputValues g0 g1 g2 =
  let (i0, g0') = withDRG g0 randomInputs
      (i1, g1') = withDRG g1 randomInputs
      i2 = zipWith3 (\x y z -> x - y - z) inputValues i0 i1
      v0 = View (Map.fromList (zip inputs i0)) g0' g0'
      v1 = View (Map.fromList (zip inputs i1)) g1' g1'
      v2 = View (Map.fromList (zip inputs i2)) g2 g2
  in foldl' (\(!v0, !v1, !v2) (i, g) -> step i g v0 v1 v2) (v0, v1, v2) assignments
  where randomInputs :: (MonadRandom m, RandomElement f) => m [f]
        randomInputs = replicateM (length inputs) randomElement
