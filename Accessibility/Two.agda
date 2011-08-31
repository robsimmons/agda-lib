-- Accessibility on 2-element sets
-- Robert J. Simmons

module Accessibility.Two where

open import Prelude
open import Accessibility.Inductive

data Two : Set where
   α : Two
   β : Two

_≡?_ : (w w' : Two) → Decidable (w ≡ w')
α ≡? α = Inl refl
α ≡? β = Inr (λ ())
β ≡? α = Inr (λ ())
β ≡? β = Inl refl

data _≺_ : Two → Two → Set where
   αβ : α ≺ β 

ind : (P : Two → Set) 
   → ((w : Two) → ((w' : Two) → w ≺ w' → P w') → P w)
   → ((w : Two) → P w)
ind P ih β = ih β (λ w' ())
ind P ih α = ih α lem
 where
   lem : (w' : Two) → α ≺ w' → P w'
   lem ._ αβ = ih β (λ w' → λ ())

Tiny : UpwardsWellFounded
Tiny = record {W = Two; _≺_ = _≺_ ; _≡?_ = _≡?_ ; ind = ind}