{-# OPTIONS --universe-polymorphism #-}

module Lib.InList where 

open import Lib.Id
open import Lib.Product
open import Lib.ListCore

module InList where

  infixr 4 _∈_

  data _∈_ {a} {A : Set a} : A → List A → Set a where
    Z : ∀{x xs} → x ∈ xs 
    S : ∀{x y xs} (n : x ∈ xs) → x ∈ y :: xs
  In : ∀{a} {A : Set a} → A → List A → Set a
  In x xs = x ∈ xs

  _⊆_ : ∀{a} {A : Set a} → List A → List A → Set a
  xs ⊆ ys = ∀{x} → x ∈ xs → x ∈ ys

  Sub : ∀{a} {A : Set a} → List A → List A → Set a
  Sub xs ys = xs ⊆ ys
 
open InList public
  using (_∈_ ; _⊆_ ; Z ; S ; In ; Sub)


  
    