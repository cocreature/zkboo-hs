{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
import           Data.Proxy
import           Control.Monad
import           GHC.TypeLits
import           Crypto.Random
import           Data.Traversable
import           Hedgehog hiding (eval)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import           Test.Tasty
import           Test.Tasty.Hedgehog

import           Crypto.ZKBoo
import           Crypto.ZKBoo.Util

main :: IO ()
main =
  defaultMain $
  testGroup
    "tasty-hedgehog tests"
    [ testProperty "decompose" prop_decompose_eval_equivalent
    ]

prop_decompose_eval_equivalent :: Property
prop_decompose_eval_equivalent =
  property $ do
    circuit <- forAll (genCircuit genZN :: Gen (Circuit (ZN 2)))
    inputValues <- forAll (replicateM (length (inputs circuit)) genZN)
    g0 <- drgNewSeed . seedFromInteger <$> forAll (Gen.integral (Range.linear 1 (10 ^ (6 :: Int))))
    g1 <- drgNewSeed . seedFromInteger <$> forAll (Gen.integral (Range.linear 1 (10 ^ (6 :: Int))))
    g2 <- drgNewSeed . seedFromInteger <$> forAll (Gen.integral (Range.linear 1 (10 ^ (6 :: Int))))
    let (v0, v1, v2) = decomposeEval circuit inputValues g0 g1 g2
    eval circuit inputValues === output (outputs circuit) v0 v1 v2

genExpr :: Gen f -> Int -> Gen (Expr f)
genExpr genF numGates =
  Gen.choice
    [ AddConst <$> gateId <*> genF
    , MultConst <$> gateId <*> genF
    , Add <$> gateId <*> gateId
    , Mult <$> gateId <*> gateId
    ]
  where
    gateId = GateId <$> Gen.integral (Range.constant 0 (numGates - 1))

genCircuit :: Gen f -> Gen (Circuit f)
genCircuit genF = do
  numInputs <- Gen.integral (Range.linear 1 10)
  let inputIds = map GateId [0..numInputs - 1]
  numGates <- Gen.integral (Range.linear 0 50)
  gateAssignments <- for [numInputs .. numInputs + numGates - 1] $ \i -> do
    expr <- genExpr genF i
    pure (GateId i, expr)
  outputIds <-
    map GateId <$>
    Gen.list
      (Range.linear 1 10)
      (Gen.integral (Range.constant 0 (numInputs + numGates - 1)))
  pure (Circuit inputIds outputIds gateAssignments)

genZN :: forall n. KnownNat n => Gen (ZN n)
genZN = fromInteger <$> Gen.integral (Range.linear 0 (natVal (Proxy :: Proxy n)))
