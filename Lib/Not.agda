{-# OPTIONS --universe-polymorphism #-}

module Lib.Not where

open import Lib.Sum

Not : ∀ {a} → Set a → Set a
Not A = A → ⊥

¬ : ∀ {a} → Set a → Set a
¬ A = A → ⊥ 

Decidable : ∀ {a} → Set a → Set a
Decidable A = A + ¬ A