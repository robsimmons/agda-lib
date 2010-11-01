{-# OPTIONS --universe-polymorphism #-}

module Lib.PiList where

open import Lib.List

module PiList where

  data PiList {a} {A : Set a} (P : A → Set a) : ListT A → Set a where
    [] : PiList P []
    _::_ : ∀{x xs} (px : P x) (pxs : PiList P xs) → PiList P (x :: xs)
 
  pull : ∀{a} {A : Set a} {x : A} {xs : ListT A} {P : A → Set a} 
     → x ∈ xs 
     → PiList P xs 
     → P x
  pull Z (px :: pxs) = px
  pull (S n) (px :: pxs) = pull n pxs
    
open PiList public
  using ([] ; _::_)
  renaming (PiList to PiListT)


data In {a} {A : Set a} {P : A → Set a} : {x : A} {xs : ListT A} → P x → PiListT P xs → Set a where
  Z : ∀{x xs} {px : P x} {pxs : PiListT P xs} → In px (px :: pxs)
  S : ∀{x y xs} {px : P x} {py : P y} {pxs : PiListT P xs}
     (n : In px pxs)
     → In px (py :: pxs)

Sub : ∀{a} {A : Set a} {xs ys : ListT A} {P : A → Set a} 
   → PiListT P xs 
   → PiListT P ys 
   → Set a
Sub {P = P} pxs pys = {x : _} {px : P x} → In px pxs → In px pys

{-
_⊆_ : ∀{a} {A : Set a} → List A → List A → Set a
xs ⊆ ys = ∀{x} → x ∈ xs → x ∈ ys

Sub : ∀{a} {A : Set a} → List A → List A → Set a
Sub xs ys = xs ⊆ ys
-}