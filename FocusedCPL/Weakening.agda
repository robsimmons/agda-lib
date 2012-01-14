-- Constructive Provability Logic
-- Focused variant
-- Robert J. Simmons, Bernardo Toninho

-- Master induction hypothesis for cut elimination

open import Prelude hiding (⊥; [_])
open import Accessibility.Inductive
open import Accessibility.IndexedList
open import FocusedCPL.Core

module FocusedCPL.Weakening where

module WEAKENING (UWF : UpwardsWellFounded) where
  open TRANS-UWF UWF
  open ILIST UWF
  open SEQUENT UWF

  wk : ∀{א א' Γ Γ' w Form}
    → LIST.SET.Sub א א'
    → Γ ⊆ Γ' to w
    → Exp א Γ w Form
    → Exp א Γ' w Form
  wk = ind+ wkP {!!} _ ≺*≡
   where
    wkP : W → Set
    wkP = λ w' → ∀{א א' Γ Γ' w Form}
      → w' ≺* w
      → LIST.SET.Sub א א'
      → Γ ⊆ Γ' to w'
      → Exp א Γ w Form
      → Exp א Γ' w Form
    
    wk' : (w : W) → ((w' : W) → w ≺+ w' → wkP w') → wkP w
    --
    wk' w ih ω ρ θ (pR x) = pR (⊆to* ω θ x)
    wk' w ih ω ρ θ (↓R N₁) = ↓R (wk' w ih ω ρ θ N₁)
    wk' w ih ω ρ θ (◇R ω' N₁) = ◇R ω' (wk' w ih (≺*+ (≺*S' ω ω')) ρ θ N₁)
    wk' w ih ω ρ θ (□R N₁) = □R λ ω' → wk' w ih (≺*+ (≺*S' ω ω')) ρ θ (N₁ ω')
    --
    wk' w ih ω ρ θ (L pf⁺ N₁) = L pf⁺ (wk' w ih ω ρ (⊆to/both θ) N₁)
    wk' w ih ω ρ θ (↓L pf⁻ ωh x Sp) =
      ↓L pf⁻ ωh (⊆to* (≺*trans ω ωh) θ x) (wk' w ih ω ρ θ Sp)
    wk' w ih ω ρ θ ⊥L = ⊥L
    wk' w ih ω ρ θ (◇L N₁) =
      ◇L λ ω' N₀ → wk' w ih ω ρ θ 
        (N₁ ω' (ih _ (≺*S' ω {!!}) ≺*≡ ρ (⊆to/≺+' (≺*S' ω {!ω'!}) θ) N₀))
    wk' w ih ω ρ θ (□L N₁) = 
      □L λ N₀ → wk' w ih ω ρ θ
        (N₁ λ ω' → {!!})
    wk' w ih ω ρ θ (↑R V₁) = ↑R (wk' w ih ω ρ θ V₁)
    wk' w ih ω ρ θ (⊃R N₁) = ⊃R (wk' w ih ω ρ θ N₁)
    --
    wk' w ih ω ρ θ pL = pL
    wk' w ih ω ρ θ (↑L N₁) = ↑L (wk' w ih ω ρ θ N₁)
    wk' w ih ω ρ θ (⊃L V₁ Sp₂) = ⊃L (wk' w ih {!ω!} ρ θ V₁) (wk' w ih ω ρ θ Sp₂)
    --
    wk' w ih ω ρ θ (↓E x) = ↓E (⊆to* ω θ x)
    wk' w ih ω ρ θ (Cut N) = Cut (wk' w ih ω ρ θ N)
    wk' w ih ω ρ θ (⊃E R V) = ⊃E (wk' w ih ω ρ θ R) (wk' w ih ω ρ θ V)
