module Routing.Match where

import Prelude

import Control.Alt (class Alt, (<|>))
import Control.Alternative (class Alternative)
import Control.Plus (class Plus)

import Data.Either (Either(..))
import Data.Foldable (foldl)
import Data.Int (fromString)
import Data.List (List(..), reverse)
import Data.Map as M
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, unwrap)
import Data.Semiring.Free (Free, free)
import Data.Tuple (Tuple(..), snd)

import Data.Validation.Semiring (V, invalid, unV)

import Global (readFloat, isNaN)

import Routing.Match.Class (class MatchClass)
import Routing.Match.Error (MatchError(..), showMatchError)
import Routing.Types (Route, RoutePart(..))

newtype Match i a = Match (Route -> Tuple i (V (Free MatchError) (Tuple Route a)))

data Input a
  = ILit String
  | Input (a -> String)
  | IEmpty

-- Manual instance due to the `Route` synonym in the above
instance newtypeMatch :: Newtype (Match (Input a) a) (List RoutePart -> Tuple Input (V (Free MatchError) (Tuple (List RoutePart) a))) where
  wrap = Match
  unwrap (Match m) = m

instance matchMatchClass :: MatchClass (Match Input) where
  lit input = Match \route ->
    case route of
      Cons (Path i) rs | i == input ->
        Tuple (ILit input) $ pure $ Tuple rs unit
      Cons (Path _) rs ->
        Tuple (ILit input) (invalid $ free $  UnexpectedPath input)
      _ ->
        Tuple (ILit input) (invalid $ free ExpectedPathPart)

  num = Match \route ->
    case route of
      Cons (Path input) rs ->
        let res = readFloat input in
        if isNaN res then
          Tuple (Input show) $ invalid $ free ExpectedNumber
        else
          Tuple (Input show) $ pure $ Tuple rs res
      _ ->
        Tuple (Input show) $ invalid $ free ExpectedNumber

  int = Match \route ->
    case route of
      Cons (Path input) rs -> case fromString input of
        Nothing -> Tuple (Input show) $ invalid $ free ExpectedInt
        Just res -> Tuple (Input show) $ pure $ Tuple rs res
      _ ->
        Tuple (Input show) $ invalid $ free ExpectedInt

  bool = Match \route ->
    case route of
      Cons (Path input) rs | input == "true" ->
        Tuple (Input show) $ pure $ Tuple rs true
      Cons (Path input) rs | input == "false" ->
        Tuple (Input show) $ pure $ Tuple rs false
      _ ->
        Tuple (Input show) $ invalid $ free ExpectedBoolean

  str = Match \route ->
    case route of
      Cons (Path input) rs ->
        Tuple (Input id) $ pure $ Tuple rs input
      _ ->
        Tuple (Input id) $ invalid $ free ExpectedString

  param key = Match \route ->
    case route of
      Cons (Query map) rs ->
        case M.lookup key map of
          Nothing ->
            Tuple (Input ?encodeKeyVal) $ invalid $ free $ KeyNotFound key
          Just el ->
            Tuple (Input ?encodeKeyVal) $ pure $ Tuple (Cons (Query <<< M.delete key $ map) rs) el
      _ ->
        Tuple (Input ?encodeKeyVal) $ invalid $ free ExpectedQuery
    where
      encodeKeyVal key val = "?" <> key <> "=" <> val

  params = Match \route ->
    case route of
      Cons (Query map) rs ->
        Tuple (Input \_ -> "") $ pure $ Tuple rs map
      _ ->
        Tuple (Input \_ -> "") $ invalid $ free ExpectedQuery

  end = Match \route ->
    case route of
      Nil -> Tuple IEmpty $ pure $ Tuple Nil unit
      _ -> Tuple IEmpty $ invalid $ free ExpectedEnd

  fail msg = Match \_ ->
    Tuple IEmpty $ invalid $ free $ Fail msg

instance matchFunctor :: Functor (Match Input) where
  map fn (Match r2e) = Match $ \r ->
    let Tuple i m = r2e r
    in Tuple i $ unV invalid (\(Tuple rs a) -> pure $ Tuple rs (fn a)) m

instance matchAlt :: Alt (Match Input) where
  alt (Match r2e1) (Match r2e2) = Match $ \r -> do
    (r2e1 r) <|> (r2e2 r)

instance matchPlus :: Plus (Match Input) where
  empty = Match $ const $ Tuple IEmpty (invalid one)

instance matchAlternative :: Alternative (Match Input)

instance matchApply :: Apply (Match Input) where
  apply (Match r2a2b) (Match r2a) =
    Match $ (\r -> unV (processFnErr r) processFnRes (r2a2b r))
    where processFnErr r err =
            invalid $ err * unV id (const one) (r2a r)
          processFnRes (Tuple rs a2b) =
            unV invalid (\(Tuple rss a) -> pure $ Tuple rss (a2b a)) (r2a rs)

instance matchApplicative :: Applicative Match where
  pure a = Match \r -> pure $ Tuple r a

-- | Matches list of matchers. Useful when argument can easy fail (not `str`)
-- | returns `Match Nil` if no matches
list :: forall a. Match a -> Match (List a)
list (Match r2a) =
  Match $ go Nil
  where go :: List a -> Route -> V (Free MatchError) (Tuple Route (List a))
        go accum r =
          unV
          (const $ pure (Tuple r (reverse accum)))
          (\(Tuple rs a) -> go (Cons a accum) rs)
          (r2a r)




-- It groups `Free MatchError` -> [[MatchError]] -map with showMatchError ->
-- [[String]] -fold with semicolon-> [String] -fold with newline-> String
runMatch :: forall i a. Match i a -> Route -> Either String a
runMatch (Match fn) route =
  unV foldErrors (Right <<< snd) $ snd $ fn route
  where
  foldErrors errs =
    Left $ foldl (\b a -> a <> "\n" <> b) "" do
      es <- reverse <$> unwrap errs
      pure $ foldl (\b a -> a <> ";" <> b) "" $ showMatchError <$>  es


-- | if we match something that can fail then we have to
-- | match `Either a b`. This function converts matching on such
-- | sum to matching on right subpart. Matching on left branch fails.
-- | i.e.
-- | ```purescript
-- | data Sort = Asc | Desc
-- | sortOfString :: String -> Either String Sort
-- | sortOfString "asc" = Right Asc
-- | sortOfString "desc" = Right Desc
-- | sortOfString _ = Left "incorrect sort"
-- |
-- | newtype Routing = Routing Sort
-- | routes :: Match Routing
-- | routes = (pure Routing) <*> (eitherMatch (sortOfString <$> var))
-- |
-- | ```
eitherMatch :: forall a b. Match (Either a b) -> Match b
eitherMatch (Match r2eab) = Match $ \r ->
  unV invalid runEither $ (r2eab r)
  where
  runEither (Tuple rs eit) =
    case eit of
      Left _ -> invalid $ free $ Fail "Nested check failed"
      Right res -> pure $ Tuple rs res

-- | useful for matching optional params at the end of a path
-- | ```
-- | optParams = maybe M.empty id <$> optionalMatch params <* end
-- | runMatch (lit "path" *> optParams) (parse id "path/?a=1")
-- | -- (Right (fromFoldable [(Tuple "a" "1")]))
-- | ```
optionalMatch :: forall i a. Match i a -> Match i (Maybe a)
optionalMatch (Match fn) = Match (\route -> 
  let Tuple i m = fn route
  in Tuple i $ unV (const $ pure (Tuple route Nothing)) (pure <<< map Just) m)
