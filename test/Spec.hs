{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
import qualified ByteString.StrictBuilder as ByteString
import           Control.Monad
import           Crypto.Number.Serialize (os2ip)
import           Crypto.Random
import qualified Data.ByteArray.Parse as Parse
import qualified Data.ByteString as ByteString
import           Data.Proxy
import           Data.Traversable
import           Data.Word
import           GHC.TypeLits
import           Hedgehog hiding (eval)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import qualified Pedersen
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
    , testProperty "roundtrip view" prop_roundtrip_view
    , testProperty "roundtrip view via integer" prop_roundtrip_view_integer
    , testProperty "schema works for a single round" prop_single_round
    , testProperty "verification fails for different result" prop_single_round_incorrect_result
    ]

prop_decompose_eval_equivalent :: Property
prop_decompose_eval_equivalent =
  property $ do
    circuit <- forAll (genCircuit genZN :: Gen (Circuit (ZN 2)))
    inputValues <- forAll (replicateM (length (inputs circuit)) genZN)
    g0 <- drgNewTest <$> forAll genSeed
    g1 <- drgNewTest <$> forAll genSeed
    g2 <- drgNewTest <$> forAll genSeed
    let views = decomposeEval circuit inputValues (g0, g1, g2)
    eval circuit inputValues === output (outputs circuit) views

prop_roundtrip_view :: Property
prop_roundtrip_view =
  property $ do
    circuit <- forAll (genCircuit genZN :: Gen (Circuit (ZN 2)))
    inputValues <- forAll (replicateM (length (inputs circuit)) genZN)
    g0 <- drgNewTest <$> forAll genSeed
    g1 <- drgNewTest <$> forAll genSeed
    g2 <- drgNewTest <$> forAll genSeed
    let (v0, v1, v2) = decomposeEval circuit inputValues (g0, g1, g2)
    roundtrip circuit v0
    roundtrip circuit v1
    roundtrip circuit v2
  where
    roundtrip circuit v =
      let v' = () <$ v
      in case deserializeView' circuit (ByteString.builderBytes (serializeView v')) of
           Parse.ParseOK bs v'' -> assert (ByteString.null bs && v' == v'')
           Parse.ParseFail s -> footnote s *> failure
           Parse.ParseMore _ -> footnote "parser expects more input" *> failure

prop_roundtrip_view_integer :: Property
prop_roundtrip_view_integer =
  property $ do
    circuit <- forAll (genCircuit genZN :: Gen (Circuit (ZN 2)))
    inputValues <- forAll (replicateM (length (inputs circuit)) genZN)
    g0 <- drgNewTest <$> forAll genSeed
    g1 <- drgNewTest <$> forAll genSeed
    g2 <- drgNewTest <$> forAll genSeed
    let (v0, v1, v2) = decomposeEval circuit inputValues (g0, g1, g2)
    roundtrip circuit v0
    roundtrip circuit v1
    roundtrip circuit v2
  where
    roundtrip circuit v =
      let v' = () <$ v
          bs = ByteString.builderBytes (serializeView v')
          i = os2ip bs
      in case deserializeView circuit i of
           Parse.ParseOK bs' v'' -> assert (ByteString.null bs' && v' == v'')
           Parse.ParseFail s -> footnote s *> failure
           Parse.ParseMore _ -> footnote "parser expects more input" *> failure

genSeed :: Gen (Word64, Word64, Word64, Word64, Word64)
genSeed = do
  w0 <- Gen.word64 Range.constantBounded
  w1 <- Gen.word64 Range.constantBounded
  w2 <- Gen.word64 Range.constantBounded
  w3 <- Gen.word64 Range.constantBounded
  w4 <- Gen.word64 Range.constantBounded
  pure (w0, w1, w2, w3, w4)

genChallenge :: Gen Challenge
genChallenge = Gen.element [One, Two, Three]

prop_single_round :: Property
prop_single_round =
  property $ do
    circuit <- forAll (genCircuit genZN :: Gen (Circuit (ZN 2)))
    inputValues <- forAll (replicateM (length (inputs circuit)) genZN)
    g0 <- drgNewTest <$> forAll genSeed
    g1 <- drgNewTest <$> forAll genSeed
    g2 <- drgNewTest <$> forAll genSeed
    globalG <- drgNewTest <$> forAll genSeed
    let views = decomposeEval circuit inputValues (g0, g1, g2)
        ((_, params), globalG') = withDRG globalG (Pedersen.setup (max 6 (serializedViewLength circuit)))
        (com, reveals) = fst $ withDRG globalG' (commit params circuit views)
        y = eval circuit inputValues
    e <- forAll genChallenge
    verify circuit y com e (selectChallenge reveals e)
      === Success

prop_single_round_incorrect_result :: Property
prop_single_round_incorrect_result =
  property $ do
    circuit <- forAll (genCircuit genZN :: Gen (Circuit (ZN 2)))
    inputValues <- forAll (replicateM (length (inputs circuit)) genZN)
    g0 <- drgNewTest <$> forAll genSeed
    g1 <- drgNewTest <$> forAll genSeed
    g2 <- drgNewTest <$> forAll genSeed
    globalG <- drgNewTest <$> forAll genSeed
    let views = decomposeEval circuit inputValues (g0, g1, g2)
        ((_, params), globalG') = withDRG globalG (Pedersen.setup (max 6 (serializedViewLength circuit)))
        (com, reveals) = fst $ withDRG globalG' (commit params circuit views)
        y = eval circuit inputValues
    y' <- forAll (Gen.filter (/= y) $ replicateM (length y) genZN)
    e <- forAll genChallenge
    verify circuit y' com e (selectChallenge reveals e)
      === Failure "Result does not match expected result."

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
