-- Constructive Provability Logic
-- Focused variant
-- Robert J. Simmons, Bernardo Toninho

-- Master induction hypothesis for cut elimination

open import Prelude hiding (⊥; [_])
open import Accessibility.Inductive
open import Accessibility.IndexedList
open import FocusedCPL.Core
open import FocusedCPL.Atomic

module FocusedCPL.Cut.IH (UWF : UpwardsWellFounded) where
open TRANS-UWF UWF 

module IH (dec≺ : (w w' : _) → Decidable (w ≺* w')) where
  open ILIST UWF
  open SEQUENT UWF
  open ATOMIC UWF

  -- Principal cuts

  Psubst⁺ : W → Set
  Psubst⁺ wc = ∀{Γ w A C}
      → wc ≺* w
      → Value [] Γ w A
      → Term [] Γ wc (I A w) (Reg C)
      → Term [] Γ wc · (Reg C)

  Psubst⁻ : W → Set
  Psubst⁻ wc = ∀{Γ w A C} 
      → (Reg C) stable⁻ 
      → wc ≺* w
      → Term [] Γ w · (Reg A)
      → Spine [] Γ w A wc (Reg C)
      → Term [] Γ wc · (Reg C)

  -- Right commutative cuts

  PrsubstV : W → Set
  PrsubstV wc = ∀{Γ w A C}
      (Γ' : MCtx)
      → wc ≺* w
      → Term [] (Γ' ++ Γ) w · (Reg A)
      → Value [] (Γ' ++ ↓ A at w :: Γ) wc C
      → Value [] (Γ' ++ Γ) wc C

  PrsubstN : W → Set
  PrsubstN wc = ∀{Γ w A C Ω} 
      (Γ' : MCtx)
      → wc ≺* w
      → Term [] (Γ' ++ Γ) w · (Reg A)
      → Term [] (Γ' ++ ↓ A at w :: Γ) wc Ω (Reg C)
      → EvidenceΩ (Γ' ++ Γ) wc Ω True
      → Term [] (Γ' ++ Γ) wc Ω (Reg C)

  PrsubstSp : W → Set
  PrsubstSp wc = ∀{Γ w wh A B C} 
      (Γ' : MCtx)
      → wc ≺* w
      → Term [] (Γ' ++ Γ) w · (Reg A)
      → Spine [] (Γ' ++ ↓ A at w :: Γ) wh B wc (Reg C)
      → EvidenceA (Γ' ++ Γ) wc B wh True
      → Spine [] (Γ' ++ Γ) wh B wc (Reg C)

  -- Left commutative cuts

  PlsubstN : W → Set
  PlsubstN wc = ∀{Γ w A C Ω} 
      (Γ' : MCtx)
      → (Reg C) stable⁻ 
      → wc ≺* w
      → Term [] (Γ' ++ Γ) w Ω (Reg (↑ A))
      → Term [] (Γ' ++ Γ) wc (I A w) (Reg C)
      → EvidenceΩ (Γ' ++ Γ) wc Ω False
      → Term [] (Γ' ++ Γ) wc Ω (Reg C)

  PlsubstSp : W → Set
  PlsubstSp wc = ∀{Γ w A B C wh} 
      (Γ' : MCtx)
      → (Reg C) stable⁻ 
      → wc ≺* w
      → Spine [] (Γ' ++ Γ) wh B w (Reg (↑ A))
      → Term [] (Γ' ++ Γ) wc (I A w) (Reg C)
      → EvidenceA (Γ' ++ Γ) wc B wh False
      → Spine [] (Γ' ++ Γ) wh B wc (Reg C)

  -- De-cuts

  PdecutV : W → Set
  PdecutV wc = ∀{Γ' Γ A w C}
    → Evidence Γ wc Γ' (A at w) 
    → Value [] (Γ' ++ Γ) wc C
    → Value [] (Γ' ++ (A at w) :: Γ) wc C

  PdecutN : W → Set
  PdecutN wc = ∀{Γ' Γ A Ω w U b} 
    → Evidence Γ wc Γ' (A at w) 
    → EvidenceΩ (Γ' ++ Γ) wc Ω b
    → Term [] (Γ' ++ Γ) wc Ω U
    → Term [] (Γ' ++ (A at w) :: Γ) wc Ω U
 
  PdecutSp : W → Set
  PdecutSp wc = ∀{Γ' Γ A B U wh w b}
    → Evidence Γ wc Γ' (A at w) 
    → EvidenceA (Γ' ++ Γ) wc B wh b
    → Spine [] (Γ' ++ Γ) wh B wc U
    → Spine [] (Γ' ++ (A at w) :: Γ) wh B wc U

  record P (wc : W) : Set where
   field 
    subst⁺ : Psubst⁺ wc
    subst⁻ : Psubst⁻ wc
    --
    rsubstV : PrsubstV wc
    rsubstN : PrsubstN wc
    rsubstSp : PrsubstSp wc
    --
    lsubstN : PlsubstN wc
    lsubstSp : PlsubstSp wc
    --
    decutV : PdecutV wc
    decutN : PdecutN wc
    decutSp : PdecutSp wc
