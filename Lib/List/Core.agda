{-# OPTIONS --universe-polymorphism #-}

module Lib.List.Core where 

open import Lib.Id
open import Lib.Product

infixr 5 _::_
infixr 5 _++_
data List {a} (A : Set a) : Set a where
  [] : List A
  _::_ : A → List A → List A

[_] : ∀{a} {A : Set a} → A → List A
[ x ] = x :: []

_++_ : ∀{a} {A : Set a} → List A -> List A -> List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)


