{-# OPTIONS --universe-polymorphism #-}

module Lib.List.In where 

open import Lib.Id
open import Lib.Product
open import Lib.Sum
open import Lib.Imp
open import Lib.Membership
open import Lib.List.Core

infixr 4 _∈_

data _∈_ {a} {A : Set a} : A → List A → Set a where
  Z : ∀{x xs} → x ∈ x :: xs 
  S : ∀{x y xs} (n : x ∈ xs) → x ∈ y :: xs
In : ∀{a} {A : Set a} → A → List A → Set a
In x xs = x ∈ xs

in-append : ∀{a} {A : Set a} 
   → {a : A} {as : List A} → a ∈ as
   → (bs : List A)
   → a ∈ as ++ bs
in-append Z bs = Z
in-append (S n) bs = S (in-append n bs)

append-in : ∀{a} {A : Set a}
   → (as : List A)
   → {b : A} {bs : List A} → b ∈ bs
   → b ∈ as ++ bs
append-in [] n = n
append-in (a :: as) n = S (append-in as n)

split-cons : ∀{a} {A : Set a} {x y : A} {ys : List A} 
   → x ∈ (y :: ys) 
   → (x ≡ y) + (x ∈ ys)
split-cons Z = Inl refl
split-cons (S n) = Inr n

case-cons : ∀{a b} {A : Set a} {x y : A} {ys : List A} 
   → (P : A → Set b)
   → x ∈ y :: ys
   → P y
   → (∀{y} → y ∈ ys → P y)
   → P x
case-cons P Z ez es = ez
case-cons P (S n) ez es = es n

split-append : ∀{a} {A : Set a} {x : A} {xs ys : List A} 
   → x ∈ (xs ++ ys)
   → (x ∈ xs) + (x ∈ ys)
split-append {xs = []} n = Inr n
split-append {xs = x :: xs} Z = Inl Z
split-append {xs = x :: xs} (S n) = case (split-append n) (Inl o S) Inr

open MEMBERSHIP List In public

set-sub-in : ∀{a} {A : Set a} {x : A} {xs : List A} → SET.Sub xs (x :: xs)
set-sub-in = S
