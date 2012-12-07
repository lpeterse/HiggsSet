{-# LANGUAGE TemplateHaskell, TypeFamilies #-}
module Data.Test where

import HiggsSet

$(createHiggsSet "MeinHiggsSet" ''Int [("foo", predicateIndex (==3))])