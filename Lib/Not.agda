{-# OPTIONS --universe-polymorphism #-}

module Lib.Not where

open import Lib.Sum

module NOT where

   Not : ∀ {a} → Set a → Set a
   Not A = A → ⊥

   ¬ : ∀ {a} → Set a → Set a
   ¬ = Not

   Decidable : ∀ {a} → Set a → Set a
   Decidable A = A + ¬ A

open NOT public