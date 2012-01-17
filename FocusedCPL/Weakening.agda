-- Constructive Provability Logic
-- Focused variant
-- Robert J. Simmons, Bernardo Toninho

-- Weakening with ⊆to

open import Prelude hiding (⊥; [_])
open import Accessibility.Inductive
open import Accessibility.IndexedList
open import FocusedCPL.Core

module FocusedCPL.Weakening where

module WEAKENING (UWF : UpwardsWellFounded) where
  open TRANS-UWF UWF
  open ILIST UWF
  open SEQUENT UWF

  data _≺'_ (wc : W) : ICtx → Set where
    · : wc ≺' ·
    I : ∀{A w} 
      (ω : wc ≺* w)
      → wc ≺' (I A w) 

  PwkV : W → Set
  PwkV wc = ∀{א Γ Γ' A}
      → Unit
      → Γ ⊆ Γ' to wc
      → Value א Γ wc A
      → Value א Γ' wc A

  PwkN : W → Set
  PwkN wc = ∀{א Γ Γ' Ω A}
      → Unit
      → Γ ⊆ Γ' to wc
      → wc ≺' Ω
      → Term א Γ wc Ω A
      → Term א Γ' wc Ω A

  PwkSp : W → Set
  PwkSp wc = ∀{א Γ Γ' wh B A}
      → Unit
      → Γ ⊆ Γ' to wc
      → wc ≺* wh
      → Spine א Γ wh B wc A
      → Spine א Γ' wh B wc A

  record Pwk (wc : W) : Set where
   field
    V : PwkV wc
    N : PwkN wc
    Sp : PwkSp wc

  module WEAKENING-LEM (wc : W) (ih : (wc' : W) → wc ≺+ wc' → Pwk wc') where

    wkV : PwkV wc
    wkN : PwkN wc
    wkSp : PwkSp wc
  
    wkV ρ θ (pR x) = pR (⊆to/now θ x)
    wkV ρ θ (↓R N₁) = ↓R (wkN ρ θ · N₁)
    wkV ρ θ (◇R ω N₁) = ◇R ω (Pwk.N (ih _ (≺+0 ω)) ρ (⊆to/≺ ω θ) · N₁)
    wkV ρ θ (□R N₁) = □R λ ω → Pwk.N (ih _ (≺+0 ω)) ρ (⊆to/≺ ω θ) · (N₁ ω)

    wkN ρ θ ω (L pf⁺ N₁) = L pf⁺ (wkN ρ (⊆to/both θ) · N₁)
    wkN ρ θ ω (↓L pf⁻ ωh x Sp) = 
      ↓L pf⁻ ωh (⊆to* ωh θ x) (wkSp ρ θ ωh Sp)
    wkN ρ θ ω ⊥L = ⊥L
    wkN ρ θ (I ω) (◇L N₁) = 
      ◇L λ ω' N₀ → wkN ρ θ · 
        (N₁ ω' (Pwk.N (ih _ (≺*S' ω ω')) ρ (⊆to/≺+' (≺*S' ω ω') θ) · N₀)) 
    wkN ρ θ (I ω) (□L N₁) = 
      □L λ N₀ → wkN ρ θ · 
        (N₁ λ ω' → 
          Pwk.N (ih _ (≺*S' ω ω')) ρ (⊆to/≺+' (≺*S' ω ω') θ) · (N₀ ω'))
    wkN ρ θ ω (↑R V₁) = ↑R (wkV ρ θ V₁)
    wkN ρ θ ω (⊃R N₁) = ⊃R (wkN ρ θ (I ≺*≡) N₁)

    wkSp ρ θ ω hyp⁻ = hyp⁻
    wkSp ρ θ ω pL = pL
    wkSp ρ θ ω (↑L N₁) = ↑L (wkN ρ θ (I ω) N₁)
    wkSp ρ θ ω (⊃L V₁ Sp₂) with ω
    ... | ≺*≡ = ⊃L (wkV ρ θ V₁) (wkSp ρ θ ω Sp₂)
    ... | (≺*+ ω') = ⊃L (Pwk.V (ih _ ω') ρ (⊆to/≺+ ω' θ) V₁) (wkSp ρ θ ω Sp₂)

  PFwk : ∀{wc} → Pwk wc
  PFwk {wc} = ind+ Pwk (λ wc ih → 
   record { 
    V = WEAKENING-LEM.wkV wc ih;
    N = WEAKENING-LEM.wkN wc ih;
    Sp = WEAKENING-LEM.wkSp wc ih }) wc
 
  wkV : ∀{wc} → PwkV wc
  wkV = Pwk.V PFwk

  wkN : ∀{wc} → PwkN wc
  wkN = Pwk.N PFwk
  
  wkSp : ∀{wc} → PwkSp wc
  wkSp = Pwk.Sp PFwk

