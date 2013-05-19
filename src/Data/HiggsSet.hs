{-# LANGUAGE CPP, TemplateHaskell, FlexibleInstances, TypeFamilies #-}
module HiggsSet where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import qualified Data.Set    as S

import Data.List (foldl')

class HiggsSet a where
  type ElemOf  a
  empty  :: a
  insert :: ElemOf a -> a -> a

  toList        :: a -> [ElemOf a]
  fromSelection :: Selection a -> a

  -- some useful "views" on a selection that are always applicable
  size   :: Selection a -> Int
  list   :: Selection a -> [ElemOf a]
  set    :: Selection a -> S.Set (ElemOf a)

  -- private methods just for use within this module
  elems :: a -> IM.IntMap (ElemOf a) 

fromList :: (HiggsSet a) => [ElemOf a] -> a
fromList ls
 = foldl (flip insert) empty ls

fromList' :: (HiggsSet a) => [ElemOf a] -> a
fromList' ls
 = foldl' (flip insert) empty ls

-- applies a filter on HiggsSet
select :: HiggsSet a => Filter a -> a -> Selection a
select (ToIntSet f) set -- TODO: ask johann about a specialised intersection intset <-> intmap
 = let filter key _ = IS.member key (f set)
       m            = IM.filterWithKey filter (elems set)
   in  m `seq` Selection (set, m)
select x set
 = select (reduce x) set
 where -- TODO: optimize
   reduce x@(ToIntSet _)     = x
   reduce All                = ToIntSet (\s-> IM.keysSet $ elems s)
   reduce (Complement x)     = let (ToIntSet s) = reduce x -- safe, is a property of reduce
                               in  ToIntSet $ s `IS.difference` IM.keysSet (elems set) -- s is always a subset of set
   reduce (Union x y)        = ToIntSet (reduce x `IS.union` reduce y)
   reduce (Intersection x y) = ToIntSet (reduce x `IS.intersection` reduce y)
   reduce (Difference x y)   = ToIntSet (reduce x `IS.difference` reduce y)


predicateIndex :: ( a -> Bool ) -> IndexDescription a
predicateIndex p
 = PredicateIndex
   { indexPredicate = p
   }

data IndexDescription a
   = PredicateIndex
     { indexPredicate :: a -> Bool 
     }

-- Template Haskell code
------------------------

newtype Selection a = Selection (a, IM.IntMap (ElemOf a))

data Filter a
  -- absolute
   = ToIntSet       (a -> IS.IntSet)
  -- relative
   | All
   | Complement   (Filter a)
   | Union        (Filter a) (Filter a)
   | Intersection (Filter a) (Filter a)
   | Difference   (Filter a) (Filter a)

assert :: (Monad m) => Bool -> String -> m ()
assert True  _       = return ()
assert False message = fail message

createHiggsSet :: String -> Name -> [(String, IndexDescription a)] -> Q [Dec]
createHiggsSet setTypeString elemTypeName indices
 = do let setTypeName = mkName setTypeString
      conName         <- newName "HiggsSet"
      elemsFieldName  <- newName "elements"
      maxKeyFieldName <- newName "maxKey"

      let indexDesignations = map fst indices
      let indexDescriptions = map snd indices
      indexFieldNames 
        <- mapM (\s-> newName $ s ++ "Index" ) indexDesignations
      let indexFieldDecls   = map ( \(n,i)-> varStrictType n $ strictType notStrict $
                                               case i of
                                                  PredicateIndex {}
                                                    -> conT ''IS.IntSet 
                                                  _ -> conT ''()
                                  ) ( zip indexFieldNames indexDescriptions )
      let indexFieldInits   = map ( \(n,i)-> fieldExp n $
                                               case i of
                                                  PredicateIndex {}
                                                    -> varE 'IS.empty 
                                                  _ -> varE '()
                                  ) ( zip indexFieldNames indexDescriptions )
      let indexFilterDecls  = concatMap
                                ( \(s,n,i)-> case i of
                                              PredicateIndex {}
                                                -> [ sigD
                                                       (mkName s)
                                                       (conT ''Filter `appT` conT setTypeName)
                                                   , valD
                                                       (varP $ mkName s)
                                                       ( normalB $
                                                           conE 'ToIntSet `appE` varE n
                                                       ) [] 
                                                   ] 
                                              _ -> [] 
                                ) ( zip3 indexDesignations indexFieldNames indexDescriptions ) 

      higgsDataDef 
        <- dataD
            ( return [] ) -- cxt
            setTypeName
            [] -- [TyVarBndr]
            [ do recC
                   conName $
                   [ return ( elemsFieldName,  NotStrict, ConT ''IM.IntMap `AppT` ConT elemTypeName )
                   , return ( maxKeyFieldName, IsStrict,  ConT ''Int )
                   ] ++ indexFieldDecls
            ] -- [Con] 
            [] -- [Name]

      higgsClassInstance
        <- instanceD
             ( return [] ) -- cxt
             ( appT
                 ( return $ ConT ''HiggsSet ) 
                 ( return $ ConT setTypeName )
             )
             [ tySynInstD
                 ''ElemOf
                 [ conT setTypeName ]
                 ( conT elemTypeName )
             -- instantiating the `empty` value
             , do valD
                    (varP $ mkName "empty")
                    ( normalB $
                        recConE 
                          conName $ 
                          [ elemsFieldName  `fieldExp` varE 'IM.empty
                          , maxKeyFieldName `fieldExp` litE (IntegerL 0)
                          ] ++ indexFieldInits
                    ) []
               -- instantiating `toList` 
             , do a <- newName "a"
                  funD
                    (mkName "toList")
                    [ clause -- :: [PatQ] -> BodyQ -> [DecQ] -> ClauseQ
                        [ varP a ]
                        ( normalB
                          $ appE (varE 'IM.elems) $ appE (varE elemsFieldName) (varE a)
                        ) []
                    ]
             , do e <- newName "e"
                  a <- newName "a"
                  funD
                    (mkName "insert")
                    [ clause
                        [ varP e, varP a ]
                        ( normalB
                          $ recUpdE
                              ( varE a )
                              [ fieldExp elemsFieldName  $ varE 'IM.insert  `appE` (varE maxKeyFieldName `appE` varE a) `appE` varE e `appE`  (varE elemsFieldName `appE` varE a) 
                              , fieldExp maxKeyFieldName $ varE 'succ `appE` (varE maxKeyFieldName `appE` varE a)
                              ]
                        ) []
                    ]
             , do valD
                    (varP $ mkName "elements")
                    ( normalB $
                        varE elemsFieldName
                    ) []
             ]

      sequence $
        [ return higgsDataDef
        , return higgsClassInstance
        ] ++ indexFilterDecls

