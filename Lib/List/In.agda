{-# OPTIONS --universe-polymorphism #-}

module Lib.List.In where 

open import Lib.Id
open import Lib.Product
open import Lib.List.Core

infixr 4 _∈_

data _∈_ {a} {A : Set a} : A → List A → Set a where
  Z : ∀{x xs} → x ∈ x :: xs 
  S : ∀{x y xs} (n : x ∈ xs) → x ∈ y :: xs
In : ∀{a} {A : Set a} → A → List A → Set a
In x xs = x ∈ xs

_⊆_ : ∀{a} {A : Set a} → List A → List A → Set a
xs ⊆ ys = ∀{x} → x ∈ xs → x ∈ ys
 
