{-# OPTIONS -XFlexibleInstances -XUndecidableInstances -XTupleSections #-}
{-# LANGUAGE TemplateHaskell, ExistentialQuantification, TypeFamilies, ScopedTypeVariables, BangPatterns #-}
module Data.HiggsSet where

import Prelude hiding (lookup)

import GHC.Exts (build)

import Control.DeepSeq
import Data.TrieMap.Representation

import Data.Maybe
import Data.List hiding (insert, null, lookup)

import Control.Applicative hiding (empty)
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Reader

import qualified Data.Set     as S
import qualified Data.IntSet  as IS
import qualified Data.Map     as M
import qualified Data.IntMap  as IM
import qualified Data.TrieMap as TM
import qualified Data.Vector  as V

import Data.Function (on)

data IndexMap i   = SingletonMap { unSingletonMap :: !(TM.TMap i Int) }
                  | MultiMap     { unMultiMap     :: !(TM.TMap i IS.IntSet) }

data HiggsSet a i = HiggsSet
                    { elements       :: !(IM.IntMap a) 
                    , maxKey         :: !Int
                    , indizes        :: !(V.Vector (IndexMap i))
                    }

instance Show (HiggsSet i a) where
  show x = "HiggsSet not yet showable!"

type HiggsQuery e i a = Reader (HiggsSet e i) a 

class Indexable a where
  type IndexOf a
  project    :: IndexOf a -> a -> [IndexOf a]

class (TM.TKey a, Ord a, Bounded a, Enum a) => Index a where
  property             :: a -> Property
  property              = const NothingSpecial

index    :: (Index i) => i -> HiggsSet a i -> IndexMap i
index i s = (indizes s) V.! (fromEnum i)

data Property         = Bijective
                      | Injective
                      | Surjective
                      | NothingSpecial

data Order            = Ascending
                      | Descending

data Margin a         = Open     { unMargin :: a }
                      | Closed   { unMargin :: a }
                      | Infinite { unMargin :: a }

data Selection k      = Nothing'
                      | Singleton    !Int
                      | Set          !IS.IntSet
                      | Everything
                      | Range        (Margin    k) (Margin    k)
                      | Union        (Selection k) (Selection k)
                      | Intersection (Selection k) (Selection k)


empty     :: forall a i.(Indexable a, Index i, IndexOf a ~ i) => HiggsSet a i
empty      = HiggsSet
             { elements = IM.empty
             , maxKey   = minBound
             , indizes  = V.fromList
                           [case property i of
                             Bijective -> SingletonMap TM.empty
                             Injective -> SingletonMap TM.empty
                             _         -> MultiMap     TM.empty
                           | i         <- [minBound..maxBound] :: [i]
                           ]
             }

size      :: HiggsSet a i -> Int
size       = IM.size . elements

-----------------

insert    :: forall a i.(Indexable a, Index i, IndexOf a ~ i) => a -> HiggsSet a i -> HiggsSet a i
insert a s = s { elements = IM.insert key a (elements s)
               , maxKey   = key
               , indizes  = V.accum 
                              (foldl' 
                                (\x y-> case x of
                                          SingletonMap m -> SingletonMap $ TM.insert y key m
                                          MultiMap     m -> MultiMap     $ TM.insertWith       
                                                                             -- unite with elements already existing at index position 
                                                                             IS.union            
                                                                             -- the index position "where"
                                                                             y 
                                                                             -- the new elements' key is the value of the index map
                                                                             (IS.singleton key) 
                                                                             -- the index (TMap i IntSet)
                                                                             m                  
                                )
                              ) 
                              (indizes s)                     -- the vector
                              [(fromEnum x, project x a) | x <- [minBound..maxBound :: i]]
                                                              -- list of index sections with index positions to add
               }
             where
               key = succ $ maxKey s

delete       :: (Indexable a, Index i, IndexOf a ~ i) =>                          HiggsQuery a i (Selection i) -> HiggsSet a i -> HiggsSet a i
delete        = update (const Nothing) 
                       
update       :: (Indexable a, Index i, IndexOf a ~ i) =>        (a -> Maybe a) -> HiggsQuery a i (Selection i) -> HiggsSet a i -> HiggsSet a i
update        = updateUnsafe [minBound..maxBound]

updateUnsafe :: (Indexable a, Index i, IndexOf a ~ i) => [i] -> (a -> Maybe a) -> HiggsQuery a i (Selection i) -> HiggsSet a i -> HiggsSet a i 
updateUnsafe ix f query
  = \s-> case runReader (query >>= resolve) s of
           Nothing'      -> s
           Singleton  x  -> g s x
           Set        xs -> foldl' g s (IS.toList xs)
           Everything    -> fromList $ mapMaybe f $ toList s
  where 
    g acc i = case IM.lookup i (elements acc) of
                Nothing -> acc
                Just a  -> 
                  case f a of
                    Nothing -> 
                      acc { elements = IM.delete i (elements acc)
                          , indizes  = V.accum
                                         (foldl'
                                           (\m k-> case m of
                                                     SingletonMap m' -> SingletonMap $ TM.delete k m'
                                                     MultiMap     m' -> MultiMap     $ TM.update
                                                                                         (\is-> let is' = IS.delete i is 
                                                                                                in  if IS.null is'
                                                                                                      then Nothing 
                                                                                                      else Just is'
                                                                                         )
                                                                                         k
                                                                                         m'
                                           )
                                         )
                                         (indizes acc)
                                         [ (fromEnum x, project x a) | x <- ix ]
                          }
                    Just a' -> 
                      acc { elements = IM.insert i a' (elements acc)
                          , indizes  = V.accum
                                         (foldl'
                                           (\m k-> case m of
                                                     SingletonMap m' -> SingletonMap $ TM.insert
                                                                                         k
                                                                                         i
                                                                                         m'
                                                     MultiMap     m' -> MultiMap     $ TM.insertWith 
                                                                                         IS.union
                                                                                         k
                                                                                         (IS.singleton i)
                                                                                         m'
                                           ) 
                                         )
                                         (V.accum
                                           (foldl'
                                             (\m k-> case m of
                                                       SingletonMap m' -> SingletonMap $ TM.delete k m'
                                                       MultiMap     m' -> MultiMap     $ TM.update
                                                                                           (\is-> let is' = IS.delete i is 
                                                                                                  in  if IS.null is' 
                                                                                                        then Nothing 
                                                                                                        else Just is'
                                                                                           )
                                                                                           k
                                                                                           m'
                                             )
                                           )
                                           (indizes acc)
                                           [ (fromEnum x, project x a) | x <- ix ]
                                         )
                                         [ (fromEnum x, project x a') | x <- ix ]
                          }


------------------

toList     :: HiggsSet a i -> [a]
toList      = IM.elems . elements

fromList   :: (Indexable a, Index i, IndexOf a ~ i) => [a] -> HiggsSet a i
fromList    = foldl' (flip insert) empty

------------------

resolve    :: forall a i.(Indexable a, Index i, IndexOf a ~ i) 
              => Selection i 
              -> HiggsQuery a i (Selection i)

resolve Nothing'
  = return Nothing'

resolve (Singleton i)
  = return (Singleton i)

resolve (Set a)            
  = if IS.null a
      then return $ Nothing'
      else return $ Set a

resolve Everything
  = return Everything

resolve (Range a b)        
  = do ind <- index (unMargin a) <$> ask
       case ind of
         SingletonMap ind1 -> do let ind2 = case a of
                                              Infinite k -> ind1
                                              _          -> let (ma,la) = TM.search (unMargin a) ind1
                                                            in  f a ma $ TM.after la
                                 let ind3 = case b of
                                              Infinite k -> ind2
                                              _          -> let (mb,lb) = TM.search (unMargin b) ind2
                                                            in  f b mb $ TM.before lb
                                 return $ case TM.elems ind3 of
                                            []  -> Nothing'
                                            [i] -> Singleton i
                                            is  -> Set $ foldl' (flip IS.insert) IS.empty is
         MultiMap     ind1 -> do let ind2 = case a of
                                              Infinite k -> ind1
                                              _          -> let (ma,la) = TM.search (unMargin a) ind1
                                                            in  f a ma $ TM.after la
                                 let ind3 = case b of
                                              Infinite k -> ind2
                                              _          -> let (mb,lb) = TM.search (unMargin b) ind2
                                                            in  f b mb $ TM.before lb
                                 return $ case TM.elems ind3 of
                                            []   -> Nothing'
                                            [is] -> Set is
                                            iss  -> Set $ foldl' IS.union IS.empty iss
  where
    f           :: Margin i -> Maybe b -> TM.TMap i b -> TM.TMap i b
    f (Closed x) = maybe id (TM.insert x)
    f _          = const id

resolve (Union a b)
  = do a <- resolve a
       case a of
         Nothing'     -> resolve b
         Singleton i  -> do b <- resolve b
                            return $ case b of
                                       Nothing'      -> Singleton i
                                       Singleton j   -> Set $ IS.fromList [i,j]
                                       Set       js  -> Set $ IS.insert i js
                                       Everything    -> Everything
         Set       is -> do b <- resolve b
                            return $ case b of
                                       Nothing'      -> Set is
                                       Singleton j   -> Set $ IS.insert j is
                                       Set       js  -> Set $ IS.union is js
                                       Everything    -> Everything
         Everything   -> return Everything

resolve (Intersection a b) 
  = do a <- resolve a
       case a of
         Nothing'     -> return a
         Singleton i  -> do b <- resolve b
                            return $ case b of
                                       Nothing'      -> Nothing'
                                       Singleton j   -> if i == j
                                                          then Singleton i
                                                          else Nothing'
                                       Set       js  -> if IS.member i js
                                                          then Singleton i
                                                          else Nothing'
                                       Everything    -> Singleton i
         Set       is -> do b <- resolve b
                            return $ case b of
                                       Nothing'      -> Nothing'
                                       Singleton j   -> if IS.member j is
                                                          then Singleton j
                                                          else Nothing'
                                       Set       js  -> Set $ IS.intersection is js
                                       Everything    -> Set is
         Everything   -> resolve b


----------------------------

nothing          :: HiggsQuery a i (Selection i)
nothing           = return Nothing'

everything       :: HiggsQuery a i (Selection i)
everything        = return Everything

equals           :: (Indexable a, Index i, IndexOf a ~ i) => i -> HiggsQuery a i (Selection i)
equals i          = return $ Range (Closed i) (Closed i)

larger           :: (Indexable a, Index i, IndexOf a ~ i) => i -> HiggsQuery a i (Selection i)
larger i          = return $ Range (Open i) (Infinite i)

smaller          :: (Indexable a, Index i, IndexOf a ~ i) => i -> HiggsQuery a i (Selection i)
smaller i         = return $ Range (Infinite i) (Open i)

union            :: HiggsQuery a i (Selection i) -> HiggsQuery a i (Selection i) -> HiggsQuery a i (Selection i)
union a b         = a >>= \a'-> b >>= \b'-> (return $ Union a' b')

intersection     :: HiggsQuery a i (Selection i) -> HiggsQuery a i (Selection i) -> HiggsQuery a i (Selection i)
intersection a b  = a >>= \a'-> b >>= \b'-> (return $ Intersection a' b')

----------------------------

querySize       :: (Indexable a, Index i, IndexOf a ~ i) => HiggsQuery a i (Selection i) -> HiggsSet a i -> Int
querySize q s    = case runReader (q >>= resolve) s of
                     Nothing'     -> 0
                     Singleton i  -> 1
                     Set       is -> IS.size is
                     Everything   -> IM.size (elements s)

querySet        :: (Indexable a, Ord a, Index i, IndexOf a ~ i) => HiggsQuery a i (Selection i) -> HiggsSet a i -> S.Set a
querySet q s     = S.fromList $ queryList q s 

queryList       :: (Indexable a, Index i, IndexOf a ~ i) => HiggsQuery a i (Selection i) -> HiggsSet a i -> [a]
queryList q s    = case runReader (q >>= resolve) s of
                     Nothing'      -> []
                     Singleton i   -> return $ fromMaybe (error "corrupted HiggsSet (error 2a)") $ IM.lookup i (elements s)
                     Set       is  -> map 
                                        (\i->  fromMaybe (error "corrupted HiggsSet (error 2b)") $ IM.lookup i (elements s))
                                        (IS.toList is)
                     Everything    -> toList s

---------------------------

lookup             :: (Indexable a, Index i, IndexOf a ~ i) =>                          i -> HiggsSet a i -> Maybe a
lookup i s          = case queryList (equals i) s of
                        []    -> Nothing
                        (x:_) -> Just x

updateLookup       :: (Indexable a, Index i, IndexOf a ~ i) =>        (a -> Maybe a) -> i -> HiggsSet a i -> (Maybe a, HiggsSet a i)
updateLookup        = updateLookupUnsafe [minBound..maxBound]

updateLookupUnsafe :: (Indexable a, Index i, IndexOf a ~ i) => [i] -> (a -> Maybe a) -> i -> HiggsSet a i -> (Maybe a, HiggsSet a i)
updateLookupUnsafe ix f i s
                    = case lookup i s of
                        Nothing -> (Nothing, s)
                        Just a  -> (f a, updateUnsafe ix f (equals i) s)

-- Keys are in Trie order
-- assocs might be empty
-- order of value list is arbitrary

groupOver         :: forall a i. (Indexable a, Index i, IndexOf a ~ i) 
                     => Order 
                     -> HiggsQuery a i (Selection i) 
                     -> [(Margin i, Margin i)] 
                     -> HiggsSet a i 
                     -> [(i,[a])]

groupOver order query intervals s 
  = concatMap 
     (f (runReader (query >>= resolve) s)) 
     intervals
    where
       f selection (a, b) 
                  = case index (unMargin a) s of
                      SingletonMap ind1 -> let    ind2      = case a of
                                                                Infinite k -> ind1
                                                                _          -> let (ma,la) = TM.search (unMargin a) ind1
                                                                              in  t a ma $ TM.after la
                                           in let ind3      = case b of
                                                                Infinite k -> ind2
                                                                _          -> let (mb,lb) = TM.search (unMargin b) ind2
                                                                              in  t b mb $ TM.before lb
                                           in let traverse  = case order of
                                                                Ascending  -> TM.assocs
                                                                Descending -> toListDesc
                                           in case selection of
                                                Nothing'     -> map 
                                                                  (\(k,_)->(k,[]))
                                                                  (traverse ind3)
                                                Singleton i  -> map
                                                                  (\(k,y)->(k,) $ if i == y
                                                                                    then [fromMaybe (error "corrupted HiggsSet (error 3a)") $ IM.lookup i (elements s)]
                                                                                    else []
                                                                  )
                                                                  (traverse ind3)
                                                Set       is -> map
                                                                  (\(k,y)->(k,) $ if IS.member y is
                                                                                    then [fromMaybe (error "corrupted HiggsSet (error 3b)") $ IM.lookup y (elements s)]
                                                                                    else []
                                                                  )
                                                                  (traverse ind3)
                                                Everything   -> map
                                                                  (\(k,y)->(k,) $        [fromMaybe (error "corrupted HiggsSet (error 3c)") $ IM.lookup y (elements s)]
                                                                  )
                                                                  (traverse ind3)
                      MultiMap     ind1 -> let    ind2      = case a of
                                                                Infinite k -> ind1
                                                                _          -> let (ma,la) = TM.search (unMargin a) ind1
                                                                              in  t a ma $ TM.after la
                                           in let ind3      = case b of
                                                                Infinite k -> ind2
                                                                _          -> let (mb,lb) = TM.search (unMargin b) ind2
                                                                              in  t b mb $ TM.before lb
                                           in let traverse  = case order of
                                                                Ascending  -> TM.assocs
                                                                Descending -> toListDesc
                                           in case selection of
                                                Nothing'     -> map 
                                                                  (\(k,_)->(k,[]))
                                                                  (traverse ind3)
                                                Singleton i  -> map
                                                                  (\(k,y)->(k,) $ if IS.member i y
                                                                                    then [fromMaybe (error "corrupted HiggsSet (error 3d)") $ IM.lookup i (elements s)]
                                                                                    else []
                                                                  )
                                                                  (traverse ind3)
                                                Set       is -> map
                                                                  (\(k,y)->(k,) $ map 
                                                                                    (fromMaybe (error "corrupted HiggsSet (error 3e)") . ((flip IM.lookup) (elements s)))
                                                                                    (IS.toList $ IS.intersection is y)
                                                                  )
                                                                  (traverse ind3)
                                                Everything   -> map
                                                                  (\(k,y)->(k,) $ map 
                                                                                    (fromMaybe (error "corrupted HiggsSet (error 3f)") . ((flip IM.lookup) (elements s)))
                                                                                    (IS.toList y)
                                                                  )
                                                                  (traverse ind3)
       t            :: Margin i -> Maybe b -> TM.TMap i b -> TM.TMap i b
       t (Closed x)  = maybe id (TM.insert x)
       t _           = const id

toListDesc  :: (TM.TKey i) => TM.TMap i a -> [(i,a)]
toListDesc m = build (\ c n -> TM.foldlWithKey (\z x y-> (curry c) x y z) n m)

-- Instances

instance (Indexable a, Index i, IndexOf a ~ i, NFData a, NFData i) => NFData (HiggsSet a i) where
  rnf s  = (rnf $ elements s) `seq` V.foldl' (\a b-> a `seq` rnf b) () (indizes s)

instance (TM.TKey a, NFData a, NFData b) => NFData (TM.TMap a b) where
  rnf x = (rnf $ TM.assocs x) `seq` ()

instance (TM.TKey a, NFData a) => NFData (IndexMap a) where
  rnf (SingletonMap x) = rnf x `seq` ()
  rnf (MultiMap x)     = rnf x `seq` ()

