-- Accessibility relations on 5-element sets
-- Robert J. Simmons

open import Prelude
open import CPL.Accessibility.Inductive
import CPL.Accessibility.SuccStar

module CPL.Accessibility.Five where

  data Five : Set where
    α : Five
    β : Five
    γ : Five
    δ : Five
    ε : Five

  {- Wide five-element accessibility relation
   - 
   -      δ
   -   ↗   ↘ 
   - ε →→ γ →→ α   
   -   ↘   ↗ 
   -      β 
   -}

  succ◆ : Five → List Five
  succ◆ ε = δ ∷ γ ∷ β ∷ []
  succ◆ δ = [ α ]
  succ◆ γ = [ α ]
  succ◆ β = [ α ]
  succ◆ α = []

  _≺_ : Five → Five → Set
  w ≺ w' = w' ∈ succ◆ w

  -- Decidability

  _≡?_ : (w : Five) (w' : Five) → Decidable (w ≡ w')
  ε ≡? ε = inj₁ refl
  ε ≡? δ = inj₂ (λ ())
  ε ≡? γ = inj₂ (λ ())
  ε ≡? β = inj₂ (λ ())
  ε ≡? α = inj₂ (λ ())
  δ ≡? ε = inj₂ (λ ())
  δ ≡? δ = inj₁ refl
  δ ≡? γ = inj₂ (λ ())
  δ ≡? β = inj₂ (λ ())
  δ ≡? α = inj₂ (λ ())
  γ ≡? ε = inj₂ (λ ())
  γ ≡? δ = inj₂ (λ ())
  γ ≡? γ = inj₁ refl
  γ ≡? β = inj₂ (λ ())
  γ ≡? α = inj₂ (λ ())
  β ≡? ε = inj₂ (λ ())
  β ≡? δ = inj₂ (λ ())
  β ≡? γ = inj₂ (λ ())
  β ≡? β = inj₁ refl
  β ≡? α = inj₂ (λ ())
  α ≡? ε = inj₂ (λ ())
  α ≡? δ = inj₂ (λ ())
  α ≡? γ = inj₂ (λ ())
  α ≡? β = inj₂ (λ ())
  α ≡? α = inj₁ refl

  _∈?_ : (w : Five) (ws : List Five) → Decidable (w ∈ ws)
  w ∈? [] = inj₂ (λ ())
  w ∈? (w' ∷ ws) with w ≡? w' | w ∈? ws
  w ∈? (.w ∷ ws) | inj₁ refl | i2 = inj₁ i0
  w ∈? (w' ∷ ws) | inj₂ f | inj₁ iN = inj₁ (iS iN)
  w ∈? (w' ∷ ws) | inj₂ f | inj₂ g = inj₂ (notin f g)

  succα : ∀{w} → (P : Five → Set) → w ∈ [ α ] → P α → P w
  succα P i0 x = x
  succα P (iS ()) x

  indε : (P : Five → Set) 
     → ((w : Five) → ((w' : Five) → w ≺ w' → P w') → P w)
     → (w' : Five) → ε ≺ w' → P w'
  indε P iH .δ i0 = iH δ (λ w' ω → succα P ω (iH α (λ w' ())))
  indε P iH .γ (iS i0) = iH γ (λ w' ω → succα P ω (iH α (λ w' ())))
  indε P iH .β (iS (iS i0)) = iH β (λ w' ω → succα P ω (iH α (λ w' ())))
  indε P iH w (iS (iS (iS ())))

  ind : (P : Five → Set) 
     → ((w : Five) → ((w' : Five) → w ≺ w' → P w') → P w)
     → ((w : Five) → P w)
  ind P iH α = iH α (λ w' ())
  ind P iH β = iH β (λ w' ω → succα P ω (iH α (λ w' ())))
  ind P iH γ = iH γ (λ w' ω → succα P ω (iH α (λ w' ())))
  ind P iH δ = iH δ (λ w' ω → succα P ω (iH α (λ w' ())))
  ind P iH ε = iH ε (indε P iH)

  Wide : UpwardsWellFounded
  Wide =
    record {W = Five;
            _≺_ = _≺_;
            _≡?_ = _≡?_;
            ind = ind}
     
  module Wide* = Accessibility.SuccStar Wide         

  WideTrans : UpwardsWellFounded
  WideTrans = 
    record {W = Five;
            _≺_ = Wide*._≺+_;
            _≡?_ = _≡?_;
            ind = Wide*.ind+}
