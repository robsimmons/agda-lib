
module Lib.List where

module List where
  open import Lib.List.Core public
  open import Lib.List.In public
  
open List public
  using (List ; [] ; [_] ; _::_ ; _++_ ; _∈_ ; Z ; S)
