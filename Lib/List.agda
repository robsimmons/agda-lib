
module Lib.List where

module LIST where
  open import Lib.List.Core public
  open import Lib.List.In public
  
open LIST public
  using (List ; [] ; [_] ; _::_ ; _++_ ; _∈_ ; Z ; S)
