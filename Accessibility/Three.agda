-- Accessibility on 2-element sets
-- Robert J. Simmons

module Accessibility.Three where

open import Prelude
open import Accessibility.Inductive

data Three : Set where
   α : Three
   β : Three
   γ : Three

_≡?_ : (w w' : Three) → Decidable (w ≡ w')
α ≡? α = Inl refl
α ≡? β = Inr (λ ())
α ≡? γ = Inr (λ ())
β ≡? α = Inr (λ ())
β ≡? β = Inl refl
β ≡? γ = Inr (λ ())
γ ≡? α = Inr (λ ())
γ ≡? β = Inr (λ ())
γ ≡? γ = Inl refl

module SMALL-EXAMPLE where
   -- This is the small example from the IMLA submission 

   data _≺_ : Three → Three → Set where
      αβ : α ≺ β 
      αγ : α ≺ γ 
      βγ : β ≺ γ 

   ind : (P : Three → Set) 
      → ((w : Three) → ((w' : Three) → w ≺ w' → P w') → P w)
      → ((w : Three) → P w)
   ind P ih = lem
    where
     mutual
      lemα : (w : Three) → α ≺ w → P w
      lemα .β αβ = ih β lemβ
      lemα .γ αγ = ih γ lemγ

      lemβ : (w : Three) → β ≺ w → P w
      lemβ .γ βγ = ih γ lemγ

      lemγ : (w : Three) → γ ≺ w → P w
      lemγ _ ()

      lem : (w : Three) → P w
      lem α = ih α lemα
      lem β = ih β lemβ
      lem γ = ih γ lemγ

   SmallExample : UpwardsWellFounded
   SmallExample = record {W = Three; _≺_ = _≺_ ; _≡?_ = _≡?_ ; ind = ind}

open SMALL-EXAMPLE public using (αβ ; αγ ; βγ ; SmallExample)