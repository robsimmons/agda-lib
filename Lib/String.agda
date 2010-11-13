module Lib.String where

module STRING where
   postulate String : Set
   {-# BUILTIN STRING String #-}
   {-# COMPILED_TYPE String String #-}

open STRING public