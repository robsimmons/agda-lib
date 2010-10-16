-- CPL Definability of ¬□ and ¬◇
-- A Constructive Logic of Provability
-- Robert J. Simmons, Bernardo Toninho

open import Compat
open import Accessibility.Inductive 
import Accessibility.IndexedList as IndexedList 
import Basic.Core as Core 
import Basic.Sequent as Sequent
-- import Basic.NatDeduction as NatDeduction

module Basic.Negation (UWF : UpwardsWellFounded) where

  open SuccStar UWF
  open IndexedList UWF
  open Core UWF 
  open Sequent UWF 
  -- open NatDeduction UWF 

  ¬□ : Type -> Type
  ¬□ A = ◇ A ⊃ ⊥

  ¬◇ : Type -> Type
  ¬◇ A = □ A ⊃ ⊥

{-
  ¬□R : ∀{Γ A w} 
      → (∀{w'} → w ≺ w' → Γ ⇒ A [ w' ] → Void) 
      → Γ ⇒ ¬□ A [ w ]
  ¬□R D =
    ⊃R (◇L i0 (λ ω D₀ → abort (D ω (Sequent.wk UWF (⊆to/irrev (≺⊀ ω)
      (⊆to/refl _)) D₀))))
-}

  ¬□L : ∀{Γ A C w}
      → (¬□ A) at w ∈ Γ
      → ((∀{w'} → w ≺ w' → Γ ⇒ A [ w' ] → Void) → Γ ⇒ C [ w ])
      → Γ ⇒ C [ w ]
  ¬□L iN D = D (λ ω → {!!} )

{-
    ¬□L : ∀{Γ A C w}
      → (¬□ A) at w ∈ Γ
      → ((∀{w'} → w ≺ w' → Γ ⇒ A [ w' ] → Void) → Γ ⇒ C [ w ])
      → Γ ⇒ C [ w ]
    ¬◇R : ∀{Γ A w w'}
      → w ≺ w'
      → (Γ ⇒ A [ w' ] → Void)
      → Γ ⇒ ¬◇ A [ w ] 
    ¬◇L : ∀{Γ A w C}
      → (¬◇ A) at w ∈ Γ
      → (∀{w'} → w ≺ w' → (Γ ⇒ A [ w' ] → Void) → Γ ⇒ C [ w ])
      → Γ ⇒ C [ w ]
-}
  