module Diff (lineDiff3) where

import Prelude (class Eq, class Functor, class Ord, Unit, compare, map, max, otherwise, pure, unit, ($), (&&), (+), (-), (<), (<>), (==), (>))
import Data.Array as A
import Data.Foldable (all, fold, intercalate, sum)
import Data.List as L
import Data.List (List(..), (:))
import Data.Maybe (Maybe(..))
import Data.Monoid (power)
import Data.String (Pattern(..), split)
import Data.Tuple (Tuple(..), uncurry)

-- Ported from http://hackage.haskell.org/package/Diff-0.3.4/docs/src/Data-Algorithm-Diff.html
data DI = F | S | B

-- | A value is either from the 'First' list, the 'Second' or from 'Both'.
-- 'Both' contains both the left and right values, in case you are using a form
-- of equality that doesn't check all data (for example, if you are using a
-- newtype to only perform equality on side of a tuple).
data Diff a = First a | Second a | Both a a

newtype DL = DL {poi :: Int, poj :: Int, path :: List DI }

instance eqDL :: Eq DL where
  eq (DL x) (DL y) = x.poi == y.poi && x.poj == y.poj

instance ordDL :: Ord DL where
  compare (DL x) (DL y) = if x.poi == y.poi
    then y.poj `compare` x.poj
    else x.poi `compare` y.poi

canDiag :: forall a. (a -> a -> Boolean) -> Array a -> Array a -> Int -> Int -> Int -> Int -> Boolean
canDiag eq as bs lena lenb = \ i j ->
   if i < lena && j < lenb
    then case as A.!! i of
      Just x -> case bs A.!! j of
        Just y -> eq x y
        Nothing -> false
      Nothing -> false
    else false

dstep :: (Int -> Int -> Boolean) -> List DL -> List DL
dstep cd dls = case nextDLs dls of
 hd:rst -> hd:pairMaxes rst
 _ -> Nil
  where
    nextDLs :: List DL -> List DL
    nextDLs Nil = Nil
    nextDLs (DL dl:rest) = dl':dl'':nextDLs rest
      where dl'  = addsnake cd $ DL $ dl {poi=dl.poi + 1, path=(F : pdl)}
            dl'' = addsnake cd $ DL $ dl {poj=dl.poj + 1, path=(S : pdl)}
            pdl = dl.path
    pairMaxes Nil = Nil
    pairMaxes (x:Nil) = x : Nil
    pairMaxes (x:y:rest) = max x y:pairMaxes rest

addsnake :: (Int -> Int -> Boolean) -> DL -> DL
addsnake cd (DL dl) = case unit of
  _ | cd pi pj -> addsnake cd $ DL
               $ dl {poi = pi + 1, poj = pj + 1, path=(B : dl.path)}
    | otherwise -> DL dl
  where
  pi = dl.poi
  pj = dl.poj

emptyDL :: DL
emptyDL = DL {poi: 0, poj: 0, path: Nil}

lcs :: forall a. (a -> a -> Boolean) -> Array a -> Array a -> List DI
lcs eq as bs = go $ L.singleton $ addsnake cd emptyDL
  where
  go :: List DL -> List DI
  go dls = inner (\_ -> go $ dstep cd dls) dls

  inner :: (Unit -> List DI) -> List DL -> List DI
  inner cont (DL dl : dls)
    | dl.poi == lena && dl.poj == lenb = dl.path
    | otherwise = inner cont dls
  inner cont Nil = cont unit

  cd = canDiag eq as bs lena lenb
  lena = A.length as
  lenb = A.length bs

-- | Takes two lists and returns a list of differences between them. This is
-- 'getDiffBy' with '==' used as predicate.
getDiff :: forall t. (Eq t) => Array t -> Array t -> List (Diff t)
getDiff = getDiffBy (==)

-- | A form of 'getDiff' with no 'Eq' constraint. Instead, an equality predicate
-- is taken as the first argument.
getDiffBy :: forall t. (t -> t -> Boolean) -> Array t -> Array t -> List (Diff t)
getDiffBy eq a b = markup (A.toUnfoldable a) (A.toUnfoldable b) $ L.reverse $ lcs eq a b
    where markup (x:xs)   ys   (F:ds) = First x  : markup xs ys ds
          markup   xs   (y:ys) (S:ds) = Second y : markup xs ys ds
          markup (x:xs) (y:ys) (B:ds) = Both x y : markup xs ys ds
          markup _ _ _ = Nil

-- ported from http://hackage.haskell.org/package/diff3-0.3.1/docs/src/Data.Algorithm.Diff3.html#diff3

--------------------------------------------------------------------------------
-- | A hunk is a collection of changes that occur in a document. A hunk can be
-- some changes only in A, only in B, in both A & B (equally), or conflicting
-- between A, B and the original document.  All hunks take 3 constructors, which
-- are, in order - the elements in the left document, the original document, and
-- the right document. This order matches the order of parameters to 'diff3'.
data Hunk a = LeftChange (List a)
            | RightChange (List a)
            | Unchanged (List a)
            | Conflict (List a) (List a) (List a)

instance functorHunk :: Functor Hunk where
  map f (LeftChange ls) = LeftChange (map f ls)
  map f (RightChange rs) = RightChange (map f rs)
  map f (Unchanged os) = Unchanged (map f os)
  map f (Conflict ls os rs) = Conflict (map f ls) (map f os) (map f rs)

--------------------------------------------------------------------------------
-- | Perform a 3-way diff against 2 documents and the original document. This
-- returns a list of 'Hunk's, where each 'Hunk' contains the original document,
-- a change in the left or right side, or is in conflict. This can be considered
-- a \'low level\' interface to the 3-way diff algorithm - you may be more
-- interested in 'merge'.
diff3 :: forall a. (Eq a) => Array a -> Array a -> Array a -> List (Hunk a)
diff3 a o b = step (getDiff o a) (getDiff o b)
  where
    step Nil Nil = Nil
    step Nil ob = toHunk Nil ob
    step oa Nil = toHunk oa Nil
    step oa ob =
      let { hunks: conflictHunk, a: ra, b: rb } = shortestConflict oa ob
          { hunks: matchHunk, a: ra', b: rb' } = shortestMatch ra rb
      in conflictHunk <> matchHunk <> step ra' rb'

--------------------------------------------------------------------------------
toHunk :: forall a. List (Diff a) -> List (Diff a) -> List (Hunk a)
toHunk Nil Nil = Nil
toHunk a  Nil = L.singleton $ LeftChange $ takeSecond a
toHunk Nil b  = L.singleton $ RightChange $ takeSecond b
toHunk a  b
  | all isB a && all isB b = L.singleton $ Unchanged $ takeFirst a
  | all isB a = L.singleton $ RightChange $ takeSecond b
  | all isB b = L.singleton $ LeftChange $ takeSecond a
  | otherwise = L.singleton $ Conflict (takeSecond a) (takeFirst a) (takeSecond b)

takeSecond :: forall a. List (Diff a) -> List a
takeSecond Nil            = Nil
takeSecond (Second x:xs) = x:takeSecond xs
takeSecond (Both x _:xs) = x:takeSecond xs
takeSecond (_:xs)        = takeSecond xs

takeFirst :: forall a. List (Diff a) -> List a
takeFirst Nil            = Nil
takeFirst (First x :xs) = x:takeFirst xs
takeFirst (Both x _:xs) = x:takeFirst xs
takeFirst (_:xs)        = takeFirst xs

isB :: forall a. Diff a -> Boolean
isB (Both _ _) = true
isB _ = false
{-# INLINE isB #-}

--------------------------------------------------------------------------------
shortestMatch :: forall a. List (Diff a) -> List (Diff a) ->
  { hunks :: List (Hunk a)
  , a :: List (Diff a)
  , b :: List (Diff a)
  }
shortestMatch oa ob = go oa ob Nil Nil
  where
    go (x@(Both _ _):xs) (y@(Both _ _):ys) accX accY = go xs ys (accX <> L.singleton x) (accY <> L.singleton y)
    go xs ys accX accY = { hunks: toHunk accX accY, a: xs, b: ys }

--------------------------------------------------------------------------------
shortestConflict :: forall a. List (Diff a) -> List (Diff a)
  -> { hunks :: List (Hunk a)
    , a :: List (Diff a)
    , b :: List (Diff a)
    }
shortestConflict l r =
    let {abs: hunk, a: rA, b: rB} = go l r
    in {hunks: uncurry toHunk hunk, a: rA, b: rB}
  where
    go Nil b = {abs: Tuple Nil b, a: Nil, b: Nil}
    go a Nil = {abs: Tuple a Nil, a: Nil, b: Nil}
    go a b =
      let {init: as, rest: ta} = L.span isNotBoth a
          {init: bs, rest: tb} = L.span isNotBoth b
          am = sum $ map motion as
          bm = sum $ map motion bs
          Tuple as' ta' = if bm > am then incurMotion (bm-am) ta else Tuple Nil ta
          Tuple bs' tb' = if am > bm then incurMotion (am-bm) tb else Tuple Nil tb
      in if am == bm
         then {abs: Tuple as bs, a: ta, b: tb}
         else let {abs: xs, a: ys, b: zs} = go ta' tb'
          in {abs: Tuple (as <> as') (bs <> bs') <> xs, a: ys, b: zs}

    isNotBoth (Both _ _) = false
    isNotBoth _ = true

    motion (Second _) = 0
    motion _ = 1


--------------------------------------------------------------------------------
incurMotion :: forall a. Int -> List (Diff a) -> Tuple (List (Diff a)) (List (Diff a))
incurMotion _ Nil = Tuple Nil Nil
incurMotion 0 as  = Tuple Nil as
incurMotion n (a@(Both _ _):as) = Tuple (L.singleton a) Nil <> incurMotion (n - 1) as
incurMotion n (a@(First _):as) = Tuple (L.singleton a) Nil <> incurMotion (n - 1) as
incurMotion n (a:as) = Tuple (L.singleton a) Nil <> incurMotion n as

lineDiff3 :: String -> String -> String -> String
lineDiff3 xs ys zs = intercalate "\n"
  $ L.concatMap hunkToText $ diff3 (lines xs) (lines ys) (lines zs)
  where
    lines = split (Pattern "\n")

hunkToText :: Hunk String -> List String
hunkToText (LeftChange xs) = xs
hunkToText (RightChange xs) = xs
hunkToText (Unchanged xs) = xs
hunkToText (Conflict xs ys zs) = fold
  ([ pure $ power "<" 8 <> " Their change"
  , xs
  , pure $ power "|" 8
  , ys
  , pure $ power "=" 8
  , zs
  , pure $ power ">" 8 <> " Your change"
  ] :: Array (List String))
