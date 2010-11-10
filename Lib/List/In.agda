{-# OPTIONS --universe-polymorphism #-}

module Lib.List.In where 

open import Lib.Id
open import Lib.Product
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

open MEMBERSHIP List In public