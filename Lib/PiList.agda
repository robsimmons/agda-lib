{-# OPTIONS --universe-polymorphism #-}

module Lib.PiList where

open import Lib.List

module PiList where

  data PiList {a} {A : Set a} (P : A → Set a) : ListT A → Set a where
    [] : PiList P []
    _::_ : ∀{x xs} → (P x) → PiList P xs → PiList P (x :: xs)
    
open PiList public
  using ([] ; _::_)
  renaming (PiList to PiListT)
