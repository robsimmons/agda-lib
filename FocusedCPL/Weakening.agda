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
  PwkV wc = ∀{Γ Γ' A}
      → Γ ⊆ Γ' to wc
      → Value Γ wc A
      → Value Γ' wc A

  PwkN : W → Set
  PwkN wc = ∀{Γ Γ' Ω A}
      → Γ ⊆ Γ' to wc
      → wc ≺' Ω
      → Term Γ wc Ω A
      → Term Γ' wc Ω A

  PwkSp : W → Set
  PwkSp wc = ∀{Γ Γ' wh B A}
      → Γ ⊆ Γ' to wc
      → wc ≺* wh
      → Spine Γ wh B wc A
      → Spine Γ' wh B wc A

  record Pwk (wc : W) : Set where
   field
    V : PwkV wc
    N : PwkN wc
    Sp : PwkSp wc

  module WEAKENING-LEM (wc : W) (ih : (wc' : W) → wc ≺+ wc' → Pwk wc') where

    wkV : PwkV wc
    wkN : PwkN wc
    wkSp : PwkSp wc
  
    wkV θ (pR x) = pR (⊆to/now θ x)
    wkV θ (↓R N₁) = ↓R (wkN θ · N₁)
    wkV θ (◇R ω N₁) = ◇R ω (Pwk.N (ih _ (≺+0 ω)) (⊆to/≺ ω θ) · N₁)
    wkV θ (□R N₁) = □R λ ω → Pwk.N (ih _ (≺+0 ω)) (⊆to/≺ ω θ) · (N₁ ω)

    wkN θ ω (L pf⁺ N₁) = L pf⁺ (wkN (⊆to/both θ) · N₁)
    wkN θ ω (↓L pf⁻ ωh x Sp) = 
      ↓L pf⁻ ωh (⊆to* ωh θ x) (wkSp θ ωh Sp)
    wkN θ ω ⊥L = ⊥L
    wkN θ (I ω) (◇L N₁) = 
      ◇L λ ω' N₀ → wkN θ · 
        (N₁ ω' (Pwk.N (ih _ (≺*S' ω ω')) (⊆to/≺+' (≺*S' ω ω') θ) · N₀)) 
    wkN θ (I ω) (□L N₁) = 
      □L λ N₀ → wkN θ · 
        (N₁ λ ω' → 
          Pwk.N (ih _ (≺*S' ω ω')) (⊆to/≺+' (≺*S' ω ω') θ) · (N₀ ω'))
    wkN θ ω (↑R V₁) = ↑R (wkV θ V₁)
    wkN θ ω (⊃R N₁) = ⊃R (wkN θ (I ≺*≡) N₁)

    wkSp θ ω hyp⁻ = hyp⁻
    wkSp θ ω pL = pL
    wkSp θ ω (↑L N₁) = ↑L (wkN θ (I ω) N₁)
    wkSp θ ω (⊃L V₁ Sp₂) with ω
    ... | ≺*≡ = ⊃L (wkV θ V₁) (wkSp θ ω Sp₂)
    ... | (≺*+ ω') = ⊃L (Pwk.V (ih _ ω') (⊆to/≺+ ω' θ) V₁) (wkSp θ ω Sp₂)

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

