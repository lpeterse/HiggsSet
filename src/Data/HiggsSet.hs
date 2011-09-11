{-# OPTIONS -XFlexibleInstances -XUndecidableInstances -XTupleSections #-}
{-# LANGUAGE TemplateHaskell, ExistentialQuantification, TypeFamilies, ScopedTypeVariables, BangPatterns #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.HiggsSet
-- Copyright   :  (c) Lars Petersen 2011
-- License     :  BSD-style
-- Maintainer  :  info@lars-petersen.net
--
-- Since many function names clash with
-- "Prelude" names, this module is usually imported @qualified@, e.g.
--
-- >  import qualified Data.HiggsSet as HS
--
-- Throughout this documentation we'll assume that we want work on a set 
-- of the following example type and its index:
--
-- >  data Book      = Book
-- >                   { isbn      :: ISBN
-- >                   , authors   :: Set String
-- >                   , publisher :: String
-- >                   , year      :: Word
-- >                   , price     :: (Rational, Currency)
-- >                   , title     :: String
-- >                   }
-- >
-- >  data BookIndex = IIsbn             ISBN
-- >                 | IAuthor           String
-- >                 | IPriceInEuro      Rational
-- >                 | IPublisherAndYear String   Word
-- >                 | INewerThan2000 
-- >                 | ITitle            String
--
-----------------------------------------------------------------------------
module Data.HiggsSet
  ( -- * Set Type
    HiggsSet ()
    -- * Classes
  , Indexable (..)
  , Index     (..)
   -- * General information
  , size
    -- * Construction 
  , empty
  , insert
  , delete
  , update
  , updateUnsafe
    -- * Lookup
  , lookup
  , updateLookup
  , updateLookupUnsafe
   -- * Query
  , nothing
  , everything
  , equals
  , greater
  , greaterEq
  , lower
  , lowerEq
  , range
  , union
  , intersection
    -- * Query Application
  , querySize
  , querySet
  , queryList
  , groupOver
    -- * Conversion to/from List
  , toList
  , fromList
     -- * Auxillary Types
  , Property (..)
  , Order    (..)
  , Margin   (..)
  , HiggsQuery ()
  , Selection  ()
  ) where
   

import Prelude hiding (lookup)

import GHC.Exts (build)

import Control.DeepSeq
import Data.TrieMap.Representation

import Data.Maybe
import Data.List hiding (insert, null, lookup, delete, union)

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

-- | Don't rely on this. I just had no time to hide the plumbing, yet.
type HiggsQuery e i a = Reader (HiggsSet e i) a 

-- | The type to be indexed needs to be an instance of `Indexable`.
--   Furthermore you have to specify an associated type
--   as index and how the type maps to the index.
--
--   >  instance Indexable Book where
--   >    type IndexOf Book = BookIndex
--   >    project (IIsbn _)               x = [isbn x]
--   >    project (IAuthor _)             x = map IAuthor (toList $ authors x)
--   >    project (IPriceInEuro _)        x = [priceInEuro (price x)]
--   >    project (IPublisherAndYear _ _) x = [IPublisherAndYear (publisher x) (year x)]
--   >    project (INewerThan2000 _)      x = [INewerThan2000 | year x >= 2000] 
--   >    project (ITitle _)              x = map ITitle $ words $ title x 
class Indexable a where
  type IndexOf a
  project    :: IndexOf a -> a -> [IndexOf a]

-- | The associated index type needs to be an instance of `Index`.
--   First of all this means that it needs to be an instance of 
--   the context classes, whereas we exploit them a bit. 
--   Specifying properties of the indizes is optional, but might result
--   in better time/space efficiency. 
--   
--   See the example:
--
--   >  instance Bounded BookIndex where
--   >    minBound           = IIsbn  undefined
--   >    maxBound           = ITitle undefined
--   >
--   >  instance Enum    BookIndex where
--   >    fromEnum (IIsbn _)               = 0
--   >    fromEnum (IAuthor _)             = 1
--   >    fromEnum (IPriceInEuro _)        = 2
--   >    fromEnum (IPublisherAndYear _ _) = 3
--   >    fromEnum (INewerThan2000 _)      = 4
--   >    fromEnum (ITitle _)              = 5
--   >    toEnum 0 = (IIsbn undefined)              
--   >    toEnum 1 = (IAuthor undefined)            
--   >    toEnum 2 = (IPriceInEuro undefined)       
--   >    toEnum 3 = (IPublisherAndYear undefined undefined)
--   >    toEnum 4 = (INewerThan2000 undefined)     
--   >    toEnum 5 = (ITitle undefined)             
--   >
--   >  -- You may use the template haskell capabilites of TrieMap!
--   >  instance TrieMap.Repr BookIndex where
--   >    type Rep BookIndex = Either (ISBN)
--   >                                (Either (String)
--   >                                        (Either (Rational)
--   >                                                (Either (String, Word)
--   >                                                        (Either ()
--   >                                                                (Either (String)
--   >                                                                        ()
--   >                                )       )       )       )       )
--   >    toRep (IIsbn a)               = Left (toRep a)
--   >    toRep (IAuthor a)             = Right $ Left (toRep a)
--   >    toRep (IPriceInEuro a)        = Right $ Right $ Left (toRep a)
--   >    toRep (IPublisherAndYear a b) = Right $ Right $ Right $ Left $ toRep (a,b)
--   >    toRep (INewerThan2000)        = Right $ Right $ Right $ Right $ Left ()
--   >    toRep (ITitle a)              = Right $ Right $ Right $ Right $ Right $ Left (toRep a)
--   >
--   >  instance Index BookIndex where
--   >    property (IIsbn _) = Bijective
--   >    property _         = NothingSpecial
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

data Margin a         = -- | The wrapped element is not included
                        Open     a
                        -- | The wrapped element is included
                      | Closed   a
                        -- | The wrapped element just serves as a proxy. It is safe to use 'undefined'.
                      | Infinite a

unMargin (Open a)     = a
unMargin (Closed a)   = a
unMargin (Infinite a) = a

-- | Try to avoid explicit usage of the type 'Selection' in your code. It might disappear soon.
data Selection k      = Nothing'
                      | Singleton    !Int
                      | Set          !IS.IntSet
                      | Everything
                      | Range        (Margin    k) (Margin    k)
                      | Union        (Selection k) (Selection k)
                      | Intersection (Selection k) (Selection k)

-- | An empty 'HiggsSet' with empty indizes.
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

-- | /O(n)/ Count the elements within the set. Note that a 'HiggsSet' may contain elements equal according to 'Eq' more than once.
size      :: HiggsSet a i -> Int
size       = IM.size . elements

-----------------

-- | Insert an element to an 'HiggsSet'. Indexing takes place according to the class instances defined before. It is not checked whether such an element (according to 'Eq') already exists. If so, the set contains more than once afterwards. In such a case you may rather want to use 'update'.
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

-- | Delete /all/ elements that match the query. If you want to delete a single element, you should define a unique index.
delete       :: (Indexable a, Index i, IndexOf a ~ i) =>                          HiggsQuery a i (Selection i) -> HiggsSet a i -> HiggsSet a i
delete        = update (const Nothing) 
                       
-- | Update /all/ elements that match the query. If you want to update a single element, you should define a unique index. If the update function evaluates to 'Nothing' the element is removed from the set. Note that the resulting element gets completely indexed again, even if certain fields were not affected. You may want to have a look at 'updateUnsafe'.
update       :: (Indexable a, Index i, IndexOf a ~ i) =>        (a -> Maybe a) -> HiggsQuery a i (Selection i) -> HiggsSet a i -> HiggsSet a i
update        = updateUnsafe [minBound..maxBound]

-- | Like 'update', but only the supplied indizes are updated. DANGER: It is possible to corrupt the 'HiggsSet'.
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

-- |  Enumerates all elements of the set in an arbitrary order. This is meant to be the standard of export.
toList     :: HiggsSet a i -> [a]
toList      = IM.elems . elements

-- |  /Strictly/ creates an 'HiggsSet' from a list. No check for double entries. All indizes are created according to 'Indexable' class instance.
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

-- | An empty selection. Do not hesitate to use it as a base element of a 'foldl':
--
--   > foldl union nothing xs
nothing          :: HiggsQuery a i (Selection i)
nothing           = return Nothing'

-- | Select all elements. Do not hesitate to use it as a base element of a 'foldl'.
--   The selection doesn't allocate anything and is optimised away:
--
--   > foldl intersection everything xs
everything       :: HiggsQuery a i (Selection i)
everything        = return Everything

-- | Select all elements that matching the given index position.
equals           :: (Indexable a, Index i, IndexOf a ~ i) => i -> HiggsQuery a i (Selection i)
equals i          = return $ Range (Closed i) (Closed i)

-- | Select all elements that are /strictly/ greater than the given index position (only within the given subindex).
greater          :: (Indexable a, Index i, IndexOf a ~ i) => i -> HiggsQuery a i (Selection i)
greater i         = return $ Range (Open i) (Infinite i)

-- | Select all elements that are greater or equal than the given index position (only within the given subindex).
greaterEq        :: (Indexable a, Index i, IndexOf a ~ i) => i -> HiggsQuery a i (Selection i)
greaterEq i       = return $ Range (Closed i) (Infinite i)

-- | Select all elements that are /strictly/ lower than the given index position (only within the given subindex).
lower            :: (Indexable a, Index i, IndexOf a ~ i) => i -> HiggsQuery a i (Selection i)
lower i           = return $ Range (Infinite i) (Open i)

-- | Select all elements that are lower or equal than the given index position (only within the given subindex).
lowerEq          :: (Indexable a, Index i, IndexOf a ~ i) => i -> HiggsQuery a i (Selection i)
lowerEq i         = return $ Range (Infinite i) (Closed i)

-- | Selects all elements within a certain range (must not leave a subindex).
range            :: (Indexable a, Index i, IndexOf a ~ i) => Margin i -- ^ the lower margin
                                                          -> Margin i -- ^ the uppper margin
                                                          -> HiggsQuery a i (Selection i) 
range a b         = return $ Range a b 

-- | The union of two selections. The underlying representation uses patricia trees for which unions are quite efficient.
union            :: HiggsQuery a i (Selection i) -> HiggsQuery a i (Selection i) -> HiggsQuery a i (Selection i)
union a b         = a >>= \a'-> b >>= \b'-> (return $ Union a' b')

-- | The intersection of two selections. The underlying representation uses patricia trees for which intersections are quite efficient.
intersection     :: HiggsQuery a i (Selection i) -> HiggsQuery a i (Selection i) -> HiggsQuery a i (Selection i)
intersection a b  = a >>= \a'-> b >>= \b'-> (return $ Intersection a' b')


-- | Returns how many elements match a certain query.
querySize       :: (Indexable a, Index i, IndexOf a ~ i) => HiggsQuery a i (Selection i) -> HiggsSet a i -> Int
querySize q s    = case runReader (q >>= resolve) s of
                     Nothing'     -> 0
                     Singleton i  -> 1
                     Set       is -> IS.size is
                     Everything   -> IM.size (elements s)

-- | Returns all elements matching a certain query as a 'Data.Set.Set'. Double entries are removed, but construction of the set takes /O(n*log(n)/.
querySet        :: (Indexable a, Ord a, Index i, IndexOf a ~ i) => HiggsQuery a i (Selection i) -> HiggsSet a i -> S.Set a
querySet q s     = S.fromList $ queryList q s 

-- | Returns all elements matching a certain query as a list in arbitrary order. 
queryList       :: (Indexable a, Index i, IndexOf a ~ i) => HiggsQuery a i (Selection i) -> HiggsSet a i -> [a]
queryList q s    = case runReader (q >>= resolve) s of
                     Nothing'      -> []
                     Singleton i   -> return $ fromMaybe (error "corrupted HiggsSet (error 2a)") $ IM.lookup i (elements s)
                     Set       is  -> map 
                                        (\i->  fromMaybe (error "corrupted HiggsSet (error 2b)") $ IM.lookup i (elements s))
                                        (IS.toList is)
                     Everything    -> toList s


-- | Looks up an element by index position. If the index is not unique an arbitrary (but not random!) element is returned.
lookup             :: (Indexable a, Index i, IndexOf a ~ i) =>                          i -> HiggsSet a i -> Maybe a
lookup i s          = case queryList (equals i) s of
                        []    -> Nothing
                        (x:_) -> Just x

-- | Updates an element by index position and returns the updated element. If the index is not unique one arbitrary element gets updated.
--   The old element is removed from all indizes and the new one gets completely indexed. Again, see 'updateLookupUnsafe' as well.
updateLookup       :: (Indexable a, Index i, IndexOf a ~ i) =>        (a -> Maybe a) -> i -> HiggsSet a i -> (Maybe a, HiggsSet a i)
updateLookup        = updateLookupUnsafe [minBound..maxBound]

-- | Like 'updateLookup', but only the supplied indizes get updated. DANGER: This may corrupt the 'HiggsSet'.
updateLookupUnsafe :: (Indexable a, Index i, IndexOf a ~ i) => [i] -> (a -> Maybe a) -> i -> HiggsSet a i -> (Maybe a, HiggsSet a i)
updateLookupUnsafe ix f i s
                    = case lookup i s of
                        Nothing -> (Nothing, s)
                        Just a  -> (f a, updateUnsafe ix f (equals i) s)

-- | Some examples of how to use this function w.r.t. our example type:
--
--   List all books more expensive than 10 Euro by price in an ascending order. 
--
--   > let p = concatMap snd $ groupOver 
--   >                           Ascending
--   >                           everything
--   >                           [(Infinite (IPriceInEuro 10), Infinite (IPriceInEuro undefined)]
--   >                           myHiggsSet
--  
--    
--   List all books ordered by year from 1987 to 2010 which were either 
--   written by one of the Simons or have a /Haskell/ in the title and were written 
--   1990 or later. In all cases, it mustn't be more expensive than 40 Euro.
-- 
--   > let p = concatMap snd $ groupOver 
--   >                           Descending
--   >                           ( (              equals (IAuthor "S.P. Jones") 
--   >                             `union`        equals (IAuthor "S. Marlow") 
--   >                             `union`        (                equals    (ITitle "Haskell") 
--   >                                              `intersection` greaterEq (IYear 1990)
--   >                                            )
--   >                             )
--   >                             `intersection` lowerEq (IPrice 40)
--   >                           )
--   >                           [(Closed (IYear 1987), Open (IYear 2011)]
--   >                           myHiggsSet
--  
--   In certain applications one needs something that is @LIMIT@ in SQL for getting the result segmentwise.
--   In this implementation there is no better way than walking along the index. Thanks to lazyness we save
--   some lookups if we throw elements right away and don't touch them. So do your @LIMIT@ like this:
--
--   > take 10 $ drop 100 p
groupOver         :: forall a i. (Indexable a, Index i, IndexOf a ~ i) 
                     => Order                          -- ^ Whether to traverse the given index segments in 'Ascending' or 'Descending' order. 
                     -> HiggsQuery a i (Selection i)   -- ^ A selection that every element must be part of. 
                     -> [(Margin i, Margin i)]         -- ^ A list of index segments @(lowerBound, upperBound)@ that we traverse over.
                                                       --   It is not checked whether neighbouring segments overlap or are in the right order.
                     -> HiggsSet a i                   
                     -> [(i,[a])]                      -- ^ Every index positions elements got intersected with the supplied selection.
                                                       --   The associated list is in arbitrary order. Since we traverse over the whole segment
                                                       --   all index positions appear what also means that the associated list might be empty.
                                                       --   You may want to apply your favourite sorting algorithm to group\/sort on the second level.

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

