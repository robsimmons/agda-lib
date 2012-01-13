
open import Prelude hiding (⊥; [_])
open import Accessibility.Inductive
open import Accessibility.IndexedList
open import FocusedCPL.Core 

module FocusedCPL.Evidence where

module EVIDENCE (UWF : UpwardsWellFounded) where

  open TRANS-UWF UWF
  open ILIST UWF
  open CORE UWF

  data EvidenceΩ (Γ : MCtx) (wc : W) : ICtx → Set where
    · : EvidenceΩ Γ wc ·
    I≡ : ∀{A} → EvidenceΩ Γ wc (I A wc)
    I+ : ∀{A w}
      (ω : wc ≺+ w) 
      (x : A ∈ Γ)
      (Sp : Spine [] Γ w A wc B)
      → EvidenceΩ Γ wc (I A w)