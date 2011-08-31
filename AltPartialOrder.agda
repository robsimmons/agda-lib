module AltPartialOrder where

open import Prelude

open import Prelude
open import Accessibility.Inductive
open import Accessibility.IndexedList

module ALT-PARTIAL-ORDER (UWF : UpwardsWellFounded) where 

   open TRANS-UWF UWF
   open ILIST UWF

   -- The alternate definition used in the tech report is weaker than the 
   -- regular definition; 
   data _⊆_to'_ {A : Set} : IList A → IList A → W → Set where 
      st : ∀{Δ Γ w}
         → (∀{A} → A at w ∈ Δ → A at w ∈ Γ)
         → (∀{w' A} → w ≺+ w' → A at w' ∈ Δ → A at w' ∈ Γ)
         → (∀{w' A} → w ≺+ w' → A at w' ∈ Γ → A at w' ∈ Δ)
         → Δ ⊆ Γ to' w
   
   alt-sound : ∀{w A}{Γ Δ : IList A} → Γ ⊆ Δ to w → Γ ⊆ Δ to' w 
   alt-sound (st sub sub≺) = 
      st (λ x → case (sub x) (λ x' → x') (λ x' → abort (x' ≺*≡)))
        (λ x x' → case (sub x') (λ x0 → x0) (λ x0 → abort (x0 (≺*+ x))))
        (λ x x' → case (sub≺ x x') (λ x0 → x0) (λ x0 → abort (x0 (≺*≡))))
