-- Constructive Provability Logic
-- Focused variant
-- Robert J. Simmons, Bernardo Toninho

-- Propositions and the focused sequent calculus

{-# OPTIONS --no-positivity-check #-}

open import Prelude hiding (⊥)
open import Accessibility.Inductive
open import Accessibility.IndexedList

module FocusedCPL.Core where

-- Types

data Type : Polarity → Set where
  a : (Q : String) (⁼ : Polarity) → Type ⁼
  --
  ↓ : (A : Type ⁻) → Type ⁺
  ⊥ : Type ⁺
  ◇ : (A : Type ⁺) → Type ⁺
  □ : (A : Type ⁺) → Type ⁺
  --
  ↑ : (A : Type ⁺) → Type ⁻
  _⊃_ : (A : Type ⁺) (B : Type ⁻) → Type ⁻

data Conc : Set where
  Reg : (A : Type ⁻) → Conc
  Abs : (A : Type ⁻) → Conc

_stable⁻ : Conc → Set
Abs A stable⁻ = Unit
Reg (a Q .⁻) stable⁻ = Unit
Reg (↑ A) stable⁻ = Unit
Reg (A ⊃ B) stable⁻ = Void

_stable⁺ : Type ⁺ → Set
a Q .⁺ stable⁺ = Unit
↓ A stable⁺ = Unit
⊥ stable⁺ = Void
◇ A stable⁺ = Void
□ A stable⁺ = Void

module SEQUENT (UWF : UpwardsWellFounded) where
  open TRANS-UWF UWF
  open ILIST UWF

  -- Building blocks
  MCtx = IList (Type ⁺)

  fromctx : ∀{A w Item Γ} (Γ' : MCtx) 
    → Item ∈ (Γ' ++ (A at w) :: Γ) 
    → (Item ≡ (A at w)) + (Item ∈ (Γ' ++ Γ))
  fromctx [] Z = Inl Refl 
  fromctx [] (S x) = Inr x
  fromctx (A :: Γ') Z = Inr Z
  fromctx (A :: Γ') (S x) with fromctx Γ' x
  ... | Inl Refl = Inl Refl
  ... | Inr x' = Inr (S x')  

  data ICtx : Set where
    · : ICtx
    I : 
      (A : Type ⁺)
      (w : W)
      → ICtx 

  -- Sequent calculus
  data SeqForm (wc : W) : Set where 
    Rfoc : (A : Type ⁺) → SeqForm wc
    Inv : (Ω : ICtx) (U : Conc) → SeqForm wc
    Lfoc : (w : W) (A : Type ⁻) (U : Conc) → SeqForm wc
    Use : (A : Type ⁻) → SeqForm wc

  data Exp (Γ : MCtx) (wc : W) : SeqForm wc → Set

  Value : MCtx → (wc : W) → Type ⁺ → Set
  Value Γ wc A = Exp Γ wc (Rfoc A)

  Term : MCtx → (wc : W) → ICtx → Conc → Set
  Term Γ wc Ω U = Exp Γ wc (Inv Ω U)

  Spine : MCtx → (w : W) → Type ⁻ → (wc : W) → Conc → Set
  Spine Γ w A wc U = Exp Γ wc (Lfoc w A U) 

  data Exp Γ wc where

    -- Values
    -- XXX INVERSION
    pR : ∀{Q}
      (x : (a Q ⁺ at wc) ∈ Γ)
      → Value Γ wc (a Q ⁺)
    ↓R : ∀{A}
      (N₁ : Term Γ wc · (Reg A))
      → Value Γ wc (↓ A)
    ◇R : ∀{A w}
      (ω : wc ≺ w)
      (N₁ : Term Γ w · (Reg (↑ A)))
      → Value Γ wc (◇ A)
    □R : ∀{A}
      (N₁ : ∀{w} (ω : wc ≺ w) → Term Γ w · (Reg (↑ A)))
      → Value Γ wc (□ A)

    -- Terms
    L : ∀{A U wh}
      (pf⁺ : A stable⁺)
      (N₁ : Term (A at wh :: Γ) wc · U)
      → Term Γ wc (I A wh) U
    ↓L : ∀{A U wh}
      (pf⁻ : U stable⁻)
      (ωh : wc ≺* wh)
      (x : ↓ A at wh ∈ Γ)
      (Sp : Spine Γ wh A wc U)
      → Term Γ wc · U
    ⊥L : ∀{U wh}
      → Term Γ wc (I ⊥ wh) U
    ◇L : ∀{A U wh}
      (N₁ : ∀{w} (ω : wh ≺ w) (N₀ : Term Γ w · (Reg (↑ A)))
        → Term Γ wc · U)
      → Term Γ wc (I (◇ A) wh) U
    □L : ∀{A U wh}
      (N₁ : (N₀ : ∀{w} (ω : wh ≺ w) → Term Γ w · (Reg (↑ A)))
        → Term Γ wc · U)
      → Term Γ wc (I (□ A) wh) U
    ↑R : ∀{A}
      (V₁ : Value Γ wc A)
      → Term Γ wc · (Reg (↑ A))
    ⊃R : ∀{A B}
      (N₁ : Term Γ wc (I A wc) (Reg B))
      → Term Γ wc · (Reg (A ⊃ B))
    
    -- Spines
    hyp⁻ : ∀{A} 
      → Spine Γ wc A wc (Abs A)
    pL : ∀{Q}
      → Spine Γ wc (a Q ⁻) wc (Reg (a Q ⁻))
    ↑L : ∀{A U wh}
      (N₁ : Term Γ wc (I A wh) U)
      → Spine Γ wh (↑ A) wc U
    ⊃L : ∀{A B U wh}
      (V₁ : Value Γ wh A)
      (Sp₂ : Spine Γ wh B wc U)
      → Spine Γ wh (A ⊃ B) wc U


