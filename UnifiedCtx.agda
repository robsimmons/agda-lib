open import Prelude

module UnifiedCtx where

data Polarity : Set where
  ⁺ : Polarity
  ⁻ : Polarity


record UCtx (Type : Polarity → Set) : Set₁ where
  field
    Ctx : Nat → Set
    CtxScope : Nat → Set

    _⟨_⟩∈_ : ∀{N M} → M < N → Type ⁺ → Ctx N → Set

    Subst : 

    _⟦_,⟦⟧⟧ : ∀{N} → CtxScope N → Ctx N → CtxScope N
    _⟦⟦⟧,_⟧ : ∀{N} → CtxScope N → Ctx N → CtxScope N

    Reduces : ∀{M N} → N < M → Type ⁺ → Ctx M → Set
    Combines : ∀{N} → CtxScope N → Ctx N → Ctx N → Set
