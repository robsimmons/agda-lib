{-# OPTIONS --universe-polymorphism #-}

module Lib.List.Core where 

open import Lib.Id
open import Lib.Product

infixr 5 _::_
infixr 5 _++_
data List {a} (A : Set a) : Set a where
   [] : List A
   _::_ : (x : A) (xs : List A) → List A

nil : ∀{a} {A : Set a} → List A
nil = []

cons : ∀{a} {A : Set a} → A → List A → List A
cons x xs = x :: xs

[_] : ∀{a} {A : Set a} → A → List A
[ x ] = x :: []

_++_ : ∀{a} {A : Set a} → List A -> List A -> List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

append : ∀{a} {A : Set a} → List A → List A → List A
append xs ys = xs ++ ys

