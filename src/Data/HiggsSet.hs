{-# LANGUAGE CPP, TemplateHaskell, FlexibleInstances, TypeFamilies #-}
module HiggsSet where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

import qualified Data.IntMap as IM
import qualified Data.IntSet as IS

class IsHiggsSet a where
  type ElemOf  a
  empty  :: a
  toList :: a -> [ElemOf a]
  insert :: ElemOf a -> a -> a

fromList :: (IsHiggsSet a) => [ElemOf a] -> a
fromList
 = foldl (flip insert) empty

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

data Filter a
   = Filter       (a -> IS.IntSet)
   | All
   | Complement   (Filter a)
   | Union        (Filter a) (Filter a)
   | Intersection (Filter a) (Filter a)
   | Without      (Filter a) (Filter a)

assert :: (Monad m) => Bool -> String -> m ()
assert True  _       = return ()
assert False message = fail message

createHiggsSet :: String -> Name -> [(String, IndexDescription a)] -> Q [Dec]
createHiggsSet setTypeString elemTypeName indices
 = do let setTypeName = mkName setTypeString
      let selectorTypeName = mkName $ setTypeString ++ "Selector"
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
                                                           conE 'Filter `appE` varE n
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
                 ( return $ ConT ''IsHiggsSet ) 
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
             ]

      sequence $
        [ return higgsDataDef
        , return higgsClassInstance
        ] ++ indexFilterDecls


-- $(createHiggsSet "SetTypeName" ''Type ['index1, 'index2, 'index3])