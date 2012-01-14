
open import Prelude hiding (⊥; [_])
open import Accessibility.Inductive
open import Accessibility.IndexedList
open import FocusedCPL.Core 

module FocusedCPL.Evidence where

module EVIDENCE (UWF : UpwardsWellFounded) where

  open TRANS-UWF UWF
  open ILIST UWF
  open SEQUENT UWF

  data Atomic (א : FCtx) (Γ : MCtx) (wc : W) : Type ⁻ → Set where

    ↓E : ∀{A}
      (x : ↓ A at wc ∈ Γ)
      → Atomic א Γ wc A
    Cut : ∀{A} 
      (N : Term א Γ wc · (Reg A))
      → Atomic א Γ wc A
    ⊃E : ∀{A B}
      (R : Atomic א Γ wc (A ⊃ B))
      (V : Value א Γ wc A)
      → Atomic א Γ wc B


  data EvidenceA (Γ : MCtx) (wc : W) : Type ⁻ → W → Set where
    E≡ : ∀{A} → EvidenceA Γ wc A wc
    E+ : ∀{A w}
      (ω : wc ≺+ w) 
      (R : Atomic [] Γ w A)
      → EvidenceA Γ wc A w

  data EvidenceΩ (Γ : MCtx) (wc : W) : ICtx → Set where
    · : EvidenceΩ Γ wc ·
    I≡ : ∀{A} → EvidenceΩ Γ wc (I A wc)
    I+ : ∀{A w}
      (ω : wc ≺+ w) 
      (R : Atomic [] Γ w (↑ A))
      → EvidenceΩ Γ wc (I A w)

  varE : ∀{A Γ w wc} → (↓ A at w) ∈ Γ → wc ≺* w → EvidenceA Γ wc A w
  varE x ≺*≡ = E≡
  varE x (≺*+ ω) = E+ ω (↓E x)

  cutE : ∀{A Γ w wc} → Term [] Γ w · (Reg A) → wc ≺* w → EvidenceA Γ wc A w
  cutE N ≺*≡ = E≡
  cutE N (≺*+ ω) = E+ ω (Cut N)

  atmE : ∀{A Γ w wc} → EvidenceA Γ wc (↑ A) w → EvidenceΩ Γ wc (I A w)
  atmE E≡ = I≡
  atmE (E+ ω R) = I+ ω R 

  appE : ∀{A Γ w wc B} 
    → EvidenceA Γ wc (A ⊃ B) w 
    → Value [] Γ w A
    → EvidenceA Γ wc B w
  appE E≡ V = E≡
  appE (E+ ω R) V = E+ ω (⊃E R V)