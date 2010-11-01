
module Lib.List where

module List where
  open import Lib.ListCore public
  open import Lib.InList public
  
open List public
  using ([] ; [_] ; _::_ ; _++_ ; _∈_ ; _⊆_ ; Z ; S)
  renaming (List to ListT)

