-- Constructive Provability Logic
-- Focused variant
-- Robert J. Simmons, Bernardo Toninho

-- Propositions and the focused sequent calculus

{-# OPTIONS --no-positivity-check #-}

open import Prelude hiding (⊥; [_])
open import Accessibility.Inductive
open import Accessibility.IndexedList

module FocusedCPL.Core where

data Polarity : Set where
  ⁻ : Polarity
  ⁺ : Polarity

data Type : Polarity → Set where
  a : (Q : String) (⁼ : Polarity) → Type ⁼
  --
  ↑ : (A : Type ⁺) → Type ⁻
  ⊥ : Type ⁺
  ◇ : (A : Type ⁻) → Type ⁺
  □ : (A : Type ⁻) → Type ⁺
  --
  ↓ : (A : Type ⁻) → Type ⁺
  _⊃_ : (A : Type ⁺) (B : Type ⁻) → Type ⁻

module CORE (UWF : UpwardsWellFounded) where
  open TRANS-UWF UWF
  open ILIST UWF

  -- Building blocks
  FCtx = List Unit -- XXX IDENTITY
  MCtx = IList (Type ⁺)

  data ICtx (wc : W) : Set where
    · : ICtx wc
    I : 
      (A : Type ⁺)
      (w : W)
      (ω : wc ≺* w)
      → ICtx wc

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

  -- Sequent calculus
  data SeqForm (wc : W) : Set where 
    Rfoc : (A : Type ⁺) → SeqForm wc
    Inv : (Ω : ICtx wc) (U : Conc) → SeqForm wc
    Lfoc : (w : W) (A : Type ⁻) (U : Conc) (ω : wc ≺* w) → SeqForm wc

  data Exp (א : FCtx) (Γ : MCtx) (wc : W) : SeqForm wc → Set

  Value : FCtx → MCtx → (wc : W) → Type ⁺ → Set
  Value א Γ wc A = Exp א Γ wc (Rfoc A)

  Term : FCtx → MCtx → (wc : W) → ICtx wc → Conc → Set
  Term א Γ wc Ω U = Exp א Γ wc (Inv Ω U)

  Spine : FCtx → MCtx → (w : W) → Type ⁻ → (wc : W) → wc ≺* w → Conc → Set
  Spine א Γ w A wc ω U = Exp א Γ wc (Lfoc w A U ω) 

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
      (wh : wc ≺ w)
      (N₁ : Term א Γ w · (Reg A))
      → Value א Γ wc (◇ A)
    □R : ∀{A}
      (N₁ : ∀{w} (ω : wc ≺ w) → Term א Γ w · (Reg A))
      → Value א Γ wc (□ A)

    -- Terms
    L : ∀{A U wh ωh}
      (pf⁺ : A stable⁺)
      (N₁ : Term א (A at wh :: Γ) wc · U)
      → Term א Γ wc (I A wh ωh) U
    ↓L : ∀{A U wh}
      (pf⁻ : U stable⁻)
      (ωh : wc ≺* wh)
      (x : ↓ A at wh ∈ Γ)
      (Sp : Spine א Γ wh A wc ωh U)
      → Term א Γ wc · U
    ⊥L : ∀{U wh ωh}
      → Term א Γ wc (I ⊥ wh ωh) U
    ◇L : ∀{A U wh ωh}
      (N₁ : ∀{w} (ω : wh ≺ w) (N₀ : Term א Γ w · (Reg A)) → Term א Γ wc · U)
      → Term א Γ wc (I (◇ A) wh ωh) U
    □L : ∀{A U wh ωh}
      (N₁ : (N₀ : ∀{w} (ω : wh ≺ w) → Term א Γ w · (Reg A)) → Term א Γ wc · U)
      → Term א Γ wc (I (□ A) wh ωh) U
    ⊃R : ∀{A B ωh}
      (N₁ : Term א Γ wc (I A wc ωh) (Reg B))
      → Term א Γ wc · (Reg (A ⊃ B))
    
    -- Spines
    -- XXX INVERSION
    pL : ∀{Q ωh}
      → Spine א Γ wc (a Q ⁻) wc ωh (Reg (a Q ⁻))
    ↑L : ∀{A U wh ωh}
      (N₁ : Term א Γ wc (I A wh ωh) U)
      → Spine א Γ wh (↑ A) wc ωh U
      