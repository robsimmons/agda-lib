{-# OPTIONS --universe-polymorphism #-}

module Lib.InList where 

open import Lib.Id
open import Lib.Product
open import Lib.List

module InList where

  infixr 4 _∈_

  data _∈_ {a} {A : Set a} : A → ListT A → Set a where
    Z : ∀{x xs} → x ∈ xs 
    S : ∀{x y xs} → x ∈ xs → x ∈ y :: xs
  InT : ∀{a} {A : Set a} → A → ListT A → Set a
  InT x xs = x ∈ xs

  _⊆_ : ∀{a} {A : Set a} → ListT A → ListT A → Set a
  xs ⊆ ys = ∀{x} → x ∈ xs → x ∈ ys

  SubT : ∀{a} {A : Set a} → ListT A → ListT A → Set a
  SubT xs ys = xs ⊆ ys
 
  
    