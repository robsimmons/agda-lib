-- Constructive Provability Logic
-- Focused variant
-- Robert J. Simmons, Bernardo Toninho

-- Pseudo-atomic terms, which are used in the intermediate proofs as evidence
-- for provability the provability of premises at accessible worlds when 
-- crawling over spines and terms.

open import Prelude hiding (⊥)
open import Accessibility.Inductive
open import Accessibility.IndexedList
open import FocusedCPL.Core
open import FocusedCPL.Weakening

module FocusedCPL.Atomic where

module ATOMIC (UWF : UpwardsWellFounded) where
  open TRANS-UWF UWF 
  open ILIST UWF
  open SEQUENT UWF
  open WEAKENING UWF

  data Atomic (Γ : MCtx) (wc : W) : Type ⁻ → Bool → Set where
    ↓E : ∀{A b}
      (x : ↓ A at wc ∈ Γ)
      → Atomic Γ wc A b
    Cut : ∀{A} 
      (N : Term Γ wc · (Reg A)) 
      → Atomic Γ wc A True
    ⊃E : ∀{A B b}
      (R : Atomic Γ wc (A ⊃ B) b)
      (V : Value Γ wc A)
      → Atomic Γ wc B b

  -- The boolean flag is a graceless mechanism, but the point is that, if you 
  -- commit yourself to not using cut, there's a trivial "unwind" pseudo-cut. 

  unwind : ∀{Γ A U w wc}
    → U stable⁻
    → wc ≺* w
    → Atomic Γ w A False
    → Spine Γ w A wc U
    → Term Γ wc · U
  unwind pf ω (↓E x) Sp = ↓L pf ω x Sp
  unwind pf ω (⊃E R V) Sp = unwind pf ω R (⊃L V Sp) 

  subset : ∀{Γ w A b}
    → Atomic Γ w A b
    → Atomic Γ w A True
  subset (↓E x) = ↓E x
  subset (Cut N) = Cut N
  subset (⊃E R V) = ⊃E (subset R) V

  wkR : ∀{Γ Γ' wc A b}
    → Γ ⊆ Γ' to wc
    → Atomic Γ wc A b
    → Atomic Γ' wc A b
  wkR θ (↓E x) = ↓E (⊆to/now θ x)
  wkR θ (Cut N) = Cut (wkN θ · N)
  wkR θ (⊃E R V) = ⊃E (wkR θ R) (wkV θ V)

  data EvidenceA (Γ : MCtx) (wc : W) : Type ⁻ → W → Bool → Set where
    E≡ : ∀{A b} → EvidenceA Γ wc A wc b
    E+ : ∀{A w b}
      (ω : wc ≺+ w) 
      (R : Atomic Γ w A b)
      → EvidenceA Γ wc A w b

  data EvidenceΩ (Γ : MCtx) (wc : W) : ICtx → Bool → Set where
    ·t : EvidenceΩ Γ wc · True
    ·f : EvidenceΩ Γ wc · False
    I≡ : ∀{A b} → EvidenceΩ Γ wc (I A wc) b
    I+ : ∀{A w b}
      (ω : wc ≺+ w) 
      (R : Atomic Γ w (↑ A) b)
      → EvidenceΩ Γ wc (I A w) b

  varE : ∀{A Γ w wc b} → (↓ A at w) ∈ Γ → wc ≺* w → EvidenceA Γ wc A w b
  varE x ≺*≡ = E≡
  varE x (≺*+ ω) = E+ ω (↓E x)

  cutE : ∀{A Γ w wc} → Term Γ w · (Reg A) → wc ≺* w 
    → EvidenceA Γ wc A w True
  cutE N ≺*≡ = E≡
  cutE N (≺*+ ω) = E+ ω (Cut N)

  atmE : ∀{A Γ w wc b} → EvidenceA Γ wc (↑ A) w b → EvidenceΩ Γ wc (I A w) b
  atmE E≡ = I≡
  atmE (E+ ω R) = I+ ω R 

  appE : ∀{A Γ w wc B b} 
    → EvidenceA Γ wc (A ⊃ B) w b
    → Value Γ w A
    → EvidenceA Γ wc B w b
  appE E≡ V = E≡
  appE (E+ ω R) V = E+ ω (⊃E R V)

  evidenceΩ≺ : ∀{w Γ Ω b} 
    → EvidenceΩ Γ w Ω b
    → w ≺' Ω 
  evidenceΩ≺ ·t = ·
  evidenceΩ≺ ·f = ·
  evidenceΩ≺ I≡ = I ≺*≡
  evidenceΩ≺ (I+ ω R) = I (≺*+ ω)

  evidenceA≺ : ∀{w w' Γ A b}
    → EvidenceA Γ w A w' b
    → w ≺* w'
  evidenceA≺ E≡ = ≺*≡
  evidenceA≺ (E+ ω R) = ≺*+ ω


  data Evidence (Γ : MCtx) (wc : W) : MCtx → Item (Type ⁺) → Set where
    N⊀ : ∀{w A} → 
      (ω : wc ≺+ w → Void)
      → Evidence Γ wc [] (A at w)      
    N+ : ∀{w A b} → 
      (ω : wc ≺+ w)
      (pf⁺ : A stable⁺)
      (R : Atomic Γ w (↑ A) b)
      → Evidence Γ wc [] (A at w)
    C⊀ : ∀{w A Γ' Item}
      (ω : wc ≺+ w → Void)
      (edΓ : Evidence Γ wc Γ' Item) 
      → Evidence Γ wc ((A at w) :: Γ') Item
    C+ : ∀{w A Γ' Item b}
      (ω : wc ≺+ w)
      (pf⁺ : A stable⁺)
      (R : Atomic (Γ' ++ Γ) w (↑ A) b)
      (edΓ : Evidence Γ wc Γ' Item) 
      → Evidence Γ wc ((A at w) :: Γ') Item
