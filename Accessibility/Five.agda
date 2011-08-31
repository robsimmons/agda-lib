-- Some accessibility relations on 5-element sets
-- Robert J. Simmons

module Accessibility.Five where

open import Prelude
open import Accessibility.Inductive

data Five : Set where
   α : Five
   β : Five
   γ : Five
   δ : Five
   ε : Five

-- Equality on this set is decidable (dumbest theorem ever)
_≡?_ : (w : Five) (w' : Five) → Decidable (w ≡ w')
ε ≡? ε = Inl refl
ε ≡? δ = Inr (λ ())
ε ≡? γ = Inr (λ ())
ε ≡? β = Inr (λ ())
ε ≡? α = Inr (λ ())
δ ≡? ε = Inr (λ ())
δ ≡? δ = Inl refl
δ ≡? γ = Inr (λ ())
δ ≡? β = Inr (λ ())
δ ≡? α = Inr (λ ())
γ ≡? ε = Inr (λ ())
γ ≡? δ = Inr (λ ())
γ ≡? γ = Inl refl
γ ≡? β = Inr (λ ())
γ ≡? α = Inr (λ ())
β ≡? ε = Inr (λ ())
β ≡? δ = Inr (λ ())
β ≡? γ = Inr (λ ())
β ≡? β = Inl refl
β ≡? α = Inr (λ ())
α ≡? ε = Inr (λ ())
α ≡? δ = Inr (λ ())
α ≡? γ = Inr (λ ())
α ≡? β = Inr (λ ())
α ≡? α = Inl refl

module EXAMPLE where
   -- This is the default "random upwards well-founded accessibility relation"
   -- from the tech report, with δ used instead of ω and ε disconnected.
   -- 
   --     β →→→→→→ δ
   --   ↗   ↗   ↗
   -- α →→↗    γ     ε

   succ◆ : Five → List Five
   succ◆ α = β :: δ :: []
   succ◆ β = δ :: []
   succ◆ γ = δ :: []
   succ◆ δ = []
   succ◆ ε = []

   _≺_ : Five → Five → Set
   w ≺ w' = w' ∈ succ◆ w

   succδ : ∀{w} → (P : Five → Set) → w ∈ [ δ ] → P δ → P w
   succδ P Z x = x
   succδ P (S ()) x

   indα : (P : Five → Set) 
      → ((w : Five) → ((w' : Five) → w ≺ w' → P w') → P w)
      → (w' : Five) → α ≺ w' → P w'
   indα P iH .β Z     = iH β (λ w' ω → succδ P ω (iH δ (λ w ())))
   indα P iH .δ (S Z) = iH δ (λ w' ())
   indα P iH w (S (S ()))

   ind : (P : Five → Set) 
      → ((w : Five) → ((w' : Five) → w ≺ w' → P w') → P w)
      → ((w : Five) → P w)
   ind P iH α = iH α (indα P iH)
   ind P iH β = iH β (λ w' ω → succδ P ω (iH δ (λ w0 ())))
   ind P iH γ = iH γ (λ w' ω → succδ P ω (iH δ (λ w0 ())))
   ind P iH δ = iH δ (λ w' ())
   ind P iH ε = iH ε (λ w' ())

   Example : UpwardsWellFounded
   Example = record
     {W = Five;
      _≺_ = _≺_;
      _≡?_ = _≡?_;
      ind = ind}

open EXAMPLE public using (Example)

module WIDE where
   -- Wide five-element accessibility relation (and its transitive closure)
   -- 
   --      δ
   --   ↗   ↘ 
   -- ε →→ γ →→ α   
   --   ↘   ↗ 
   --      β 

   succ◆ : Five → List Five
   succ◆ ε = δ :: γ :: β :: []
   succ◆ δ = [ α ]
   succ◆ γ = [ α ]
   succ◆ β = [ α ]
   succ◆ α = []

   _≺_ : Five → Five → Set
   w ≺ w' = w' ∈ succ◆ w

   notin : ∀{A ws}{w w' : A} 
      → (w ≡ w' → Void) → (w ∈ ws → Void) → (w ∈ (w' :: ws) → Void)
   notin f g Z = f refl
   notin f g (S iN) = g iN

   _∈?_ : (w : Five) (ws : List Five) → Decidable (w ∈ ws)
   w ∈? [] = Inr (λ ())
   w ∈? (w' :: ws) with w ≡? w' | w ∈? ws
   w ∈? (.w :: ws) | Inl Refl | i2 = Inl Z
   w ∈? (w' :: ws) | Inr f | Inl iN = Inl (S iN)
   w ∈? (w' :: ws) | Inr f | Inr g = Inr (notin f g)

   succα : ∀{w} → (P : Five → Set) → w ∈ [ α ] → P α → P w
   succα P Z x = x
   succα P (S ()) x

   indε : (P : Five → Set) 
      → ((w : Five) → ((w' : Five) → w ≺ w' → P w') → P w)
      → (w' : Five) → ε ≺ w' → P w'
   indε P iH .δ Z = iH δ (λ w' ω → succα P ω (iH α (λ w' ())))
   indε P iH .γ (S Z) = iH γ (λ w' ω → succα P ω (iH α (λ w' ())))
   indε P iH .β (S (S Z)) = iH β (λ w' ω → succα P ω (iH α (λ w' ())))
   indε P iH w (S (S (S ())))

   ind : (P : Five → Set) 
      → ((w : Five) → ((w' : Five) → w ≺ w' → P w') → P w)
      → ((w : Five) → P w)
   ind P iH α = iH α (λ w' ())
   ind P iH β = iH β (λ w' ω → succα P ω (iH α (λ w' ())))
   ind P iH γ = iH γ (λ w' ω → succα P ω (iH α (λ w' ())))
   ind P iH δ = iH δ (λ w' ω → succα P ω (iH α (λ w' ())))
   ind P iH ε = iH ε (indε P iH)

   Wide : UpwardsWellFounded
   Wide = record
     {W = Five;
      _≺_ = _≺_;
      _≡?_ = _≡?_;
      ind = ind}
     
   WideTrans : UpwardsWellFounded
   WideTrans = TRANS-UWF.TransUWF Wide 

open WIDE public using (Wide ; WideTrans)