{-# LANGUAGE BangPatterns #-}
module Crypto.ZKBoo
  ( GateId(..)
  , Expr(..)
  , Circuit(..)
  , View(..)
  , decomposeEval
  , eval
  , output
  , ViewCommitment(..)
  , Commitment(..)
  ) where

import           Control.Monad
import           Crypto.Random
import           Data.List (foldl')
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Monoid

import           Crypto.ZKBoo.Util


-- | A unique identifier for a gate (inputs also count as gates).
newtype GateId = GateId Int
  deriving (Eq, Ord, Show)

-- | An expression over a ring @f@.
data Expr f =
    AddConst GateId f
  | MultConst GateId f
  | Add GateId GateId
  | Mult GateId GateId
  deriving (Show)

-- | A circuit consisting of a list of inputs, a list of gates and a list of outputs.
--
-- For a circuit to be valid, the following properties need to hold
--
-- * Assignment expressions only refer to gates that are either inputs or
-- have been previously assigned.
--
-- * There are no assignments for input values.
--
-- * No gate is assigned more than once.
--
-- * All output gates are either an input or have an explicit assignment.
data Circuit f = Circuit
  { inputs :: [GateId]
  , outputs :: [GateId]
  , assignments :: [(GateId, Expr f)]
  } deriving (Show)

-- | A view consists of a mapping from 'GateId's to values in the
-- ring @f@. Initially, the mapping only contains entries for the input
-- values.
data View f gen = View
  { values :: Map GateId f
  , randomTape :: [f] -- ^ This contains the random values that have been used in reverse order.
                      -- In particular this list is always finite.
  , gen :: gen
  }

-- | Insert a value for 'GateId' into the view.
insert :: GateId -> f -> View f gen -> View f gen
insert i v (View m g g') = View (Map.insert i v m) g g'

-- | Lookup the stored value for a given 'GateId'.
--
-- This function will fail if the view contains no value for the given 'GateId'.
(!) :: View f gen -> GateId -> f
(!) (View m _ _) i = m Map.! i

-- | Get a random ring element using the PRNG stored in the 'View'. In addition
-- to the random element, the updated view is returned.
--
-- /Caution/: Reusing the original view will result in the same number being
-- generated. If that is not intended, you need to use the new view returned
-- by this function.
getRandomElement :: (DRG gen, RandomElement f) => View f gen -> (f, View f gen)
getRandomElement (View vs tape g) =
  case withDRG g randomElement of
    (v, g') -> (v, View vs (v : tape) g')

-- | @evalGateForView gateId expr wi wi1@ evaluates the gate described by
-- @expr@ using @wi@ and its right neighbor @wi1@. The result is inserted
-- in @wi@ at @gateId@.
--
-- Note that the evaluation requires generating numbers for player i as well
-- as player i + 1. Given that it might seem surprising that we do not return
-- the new PRNG for player i + 1. However, this is precisely the right
-- thing to do here since the random value used in each round should be the
-- same regardless of whether the player is seen as player i or as player
-- i + 1. Since each player is once used as player i and player i + 1 in each
-- round, we guarantee that the PRNG is updated exactly once for all players.
evalGateForView :: (DRG gen, Num f, RandomElement f) => GateId -> Expr f -> View f gen -> View f gen -> View f gen
evalGateForView i (AddConst a alpha)  wi _   = insert i (wi ! a + alpha)  wi
evalGateForView i (MultConst a alpha) wi _   = insert i (wi ! a * alpha)  wi
evalGateForView i (Add a b)           wi _   = insert i (wi ! a + wi ! b) wi
evalGateForView i (Mult a b)          wi wi1 =
  case (getRandomElement wi, getRandomElement wi1) of
    ((ri, wi'), (ri1, wi1')) ->
      let v = wi'  ! a * wi'  ! b +
              wi1' ! a * wi'  ! b +
              wi'  ! a * wi1' ! b +
              ri - ri1
      in insert i v wi'

-- | @evalGate gateId expr (w0, w1, w2)@ performs one round in the
-- 23-decomposition by evaluating @expr@ according to the rules given by
-- linear decomposition using @(w0, w1, w2)@ as the three views.
evalGate :: (DRG gen, Num f, RandomElement f)
         => GateId -> Expr f -> (View f gen, View f gen, View f gen) -> (View f gen, View f gen, View f gen)
evalGate i gate (!w0, !w1, !w2) =
  let w0' = evalGateForView i gate w0 w1
      w1' = evalGateForView i gate w1 w2
      w2' = evalGateForView i gate w2 w0
  in (w0', w1', w2')

-- | @evalGates gates views@ evaluates the gates in order using @views@
-- as the initial views. @gates@ must be topologically sorted.
evalGates :: (DRG gen, Num f, RandomElement f)
          => [(GateId, Expr f)] -> (View f gen, View f gen, View f gen) -> (View f gen, View f gen, View f gen)
evalGates assgns views = foldl' (\views' (i,g) -> evalGate i g views') views assgns

-- | Given a list of output gates and the final views, return the
-- corresponding output values.
output :: Num f => [GateId] -> (View f gen, View f gen, View f gen) -> [f]
output os (w0, w1, w2) =
  let o1 = map (w0 !) os
      o2 = map (w1 !) os
      o3 = map (w2 !) os
  in zipWith3 (\x y z -> x + y + z) o1 o2 o3

-- | Evaluate a circuit using the given input values and initial values for
-- the PRNGS and return the final views. Combine this with 'output' to get the
-- final output values.
decomposeEval :: (DRG gen, Num f, RandomElement f) => Circuit f -> [f] -> (gen, gen, gen) -> (View f gen, View f gen, View f gen)
decomposeEval circuit inputValues (g0, g1, g2) =
  let (i0, g0') = withDRG g0 randomInputs
      (i1, g1') = withDRG g1 randomInputs
      i2 = zipWith3 (\x y z -> x - y - z) inputValues i0 i1
      v0 = View (Map.fromList (zip (inputs circuit) i0)) [] g0'
      v1 = View (Map.fromList (zip (inputs circuit) i1)) [] g1'
      v2 = View (Map.fromList (zip (inputs circuit) i2)) [] g2
  in evalGates (assignments circuit) (v0, v1, v2)
  where randomInputs :: (MonadRandom m, RandomElement f) => m [f]
        randomInputs = replicateM (length (inputs circuit)) randomElement

-- | A simple evaluation function of a circuit. This is mainly
-- intended for testing purposes.
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

-- | A commitment for a single view
data ViewCommitment c f = ViewCommitment
  { result :: [f]   -- ^ The final result computed by the circuit.
  , commitment :: c -- ^ A commitment to a view.
  }

-- | The full commitment consisting of a commitment for each of the three views.
data Commitment c f = Commitment
  { commitment0 :: !(ViewCommitment c f)
  , commitment1 :: !(ViewCommitment c f)
  , commitment2 :: !(ViewCommitment c f)
  }

instance ToBytes f => ToBytes (View f gen) where
  toBytesBuilder (View vs tape _) =
    mconcat (map toBytesBuilder (Map.elems vs)) <>
    mconcat (map toBytesBuilder tape)
