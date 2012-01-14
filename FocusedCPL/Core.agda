-- Constructive Provability Logic
-- Focused variant
-- Robert J. Simmons, Bernardo Toninho

-- Propositions and the focused sequent calculus

{-# OPTIONS --no-positivity-check #-}

open import Prelude hiding (⊥; [_])
open import Accessibility.Inductive
open import Accessibility.IndexedList

module FocusedCPL.Core where

-- Types

data Polarity : Set where
  ⁻ : Polarity
  ⁺ : Polarity

data Type : Polarity → Set where
  a : (Q : String) (⁼ : Polarity) → Type ⁼
  --
  ↓ : (A : Type ⁻) → Type ⁺
  ⊥ : Type ⁺
  ◇ : (A : Type ⁻) → Type ⁺
  □ : (A : Type ⁻) → Type ⁺
  --
  ↑ : (A : Type ⁺) → Type ⁻
  _⊃_ : (A : Type ⁺) (B : Type ⁻) → Type ⁻

data Conc : Set where
  Reg : (A : Type ⁻) → Conc
  -- XXX IDENTITY

_stable⁻ : Conc → Set
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
  FCtx = List Unit -- XXX IDENTITY
  MCtx = IList (Type ⁺)

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

  data Exp (א : FCtx) (Γ : MCtx) (wc : W) : SeqForm wc → Set

  Value : FCtx → MCtx → (wc : W) → Type ⁺ → Set
  Value א Γ wc A = Exp א Γ wc (Rfoc A)

  Term : FCtx → MCtx → (wc : W) → ICtx → Conc → Set
  Term א Γ wc Ω U = Exp א Γ wc (Inv Ω U)

  Spine : FCtx → MCtx → (w : W) → Type ⁻ → (wc : W) → Conc → Set
  Spine א Γ w A wc U = Exp א Γ wc (Lfoc w A U) 

  Atomic : FCtx → MCtx → (wc : W) → Type ⁻ → Set
  Atomic א Γ wc A = Exp א Γ wc (Use A)

  data Exp א Γ wc where

    -- Values
    -- XXX INVERSION
    pR : ∀{Q}
      (x : (a Q ⁺ at wc) ∈ Γ)
      → Value א Γ wc (a Q ⁺)
    ↓R : ∀{A}
      (N₁ : Term א Γ wc · (Reg A))
      → Value א Γ wc (↓ A)
    ◇R : ∀{A w}
      (ω : wc ≺ w)
      (N₁ : Term א Γ w · (Reg A))
      → Value א Γ wc (◇ A)
    □R : ∀{A}
      (N₁ : ∀{w} (ω : wc ≺ w) → Term א Γ w · (Reg A))
      → Value א Γ wc (□ A)

    -- Terms
    L : ∀{A U wh}
      (pf⁺ : A stable⁺)
      (N₁ : Term א (A at wh :: Γ) wc · U)
      → Term א Γ wc (I A wh) U
    ↓L : ∀{A U wh}
      (pf⁻ : U stable⁻)
      (ωh : wc ≺* wh)
      (x : ↓ A at wh ∈ Γ)
      (Sp : Spine א Γ wh A wc U)
      → Term א Γ wc · U
    ⊥L : ∀{U wh}
      → Term א Γ wc (I ⊥ wh) U
    ◇L : ∀{A U wh}
      (N₁ : ∀{w} (ω : wh ≺ w) (N₀ : Term א Γ w · (Reg A)) → Term א Γ wc · U)
      → Term א Γ wc (I (◇ A) wh) U
    □L : ∀{A U wh}
      (N₁ : (N₀ : ∀{w} (ω : wh ≺ w) → Term א Γ w · (Reg A)) → Term א Γ wc · U)
      → Term א Γ wc (I (□ A) wh) U
    ↑R : ∀{A}
      (V₁ : Value א Γ wc A)
      → Term א Γ wc · (Reg (↑ A))
    ⊃R : ∀{A B}
      (N₁ : Term א Γ wc (I A wc) (Reg B))
      → Term א Γ wc · (Reg (A ⊃ B))
    
    -- Spines
    -- XXX INVERSION
    pL : ∀{Q}
      → Spine א Γ wc (a Q ⁻) wc (Reg (a Q ⁻))
    ↑L : ∀{A U wh}
      (N₁ : Term א Γ wc (I A wh) U)
      → Spine א Γ wh (↑ A) wc U
    ⊃L : ∀{A B U wh}
      (V₁ : Value א Γ wh A)
      (Sp₂ : Spine א Γ wh B wc U)
      → Spine א Γ wh (A ⊃ B) wc U

    -- Atomic terms
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

