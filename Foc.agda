open import Prelude hiding (⊥)

module Foc where

-- Propositions and polarity

data Polarity : Set where
  ⁺ : Polarity
  ⁻ : Polarity

data Type : Polarity → Set where
  a : (Q : String) (⁼ : Polarity) → Type ⁼
  --
  ↓ : (A : Type ⁻) → Type ⁺
  ⊥ : Type ⁺
  _∨_ : (A B : Type ⁺) → Type ⁺
  ⊤⁺ : Type ⁺
  _∧⁺_ : (A B : Type ⁺) → Type ⁺
  --
  ↑ : (A : Type ⁺) → Type ⁻
  _⊃_ : (A : Type ⁺) (B : Type ⁻) → Type ⁻
  ⊤⁻ : Type ⁻
  _∧⁻_ : (A B : Type ⁻) → Type ⁻

Ctx = List (Type ⁺)

_⊆_ : Ctx → Ctx → Set
_⊆_ = LIST.SET.Sub



-- Sequent calculus

data Conc : Set where
  Abs : (A : Type ⁻) → Conc
  Reg : (A : Type ⁻) → Conc

_stable⁻ : Conc → Set
Abs A stable⁻ = Unit
Reg (a Q .⁻) stable⁻ = Unit
Reg (↑ A) stable⁻ = Unit
Reg (A ⊃ B) stable⁻ = Void
Reg ⊤⁻ stable⁻ = Void
Reg (A ∧⁻ B) stable⁻ = Void

_stable⁺ : Type ⁺ → Set
a Q .⁺ stable⁺ = Unit
↓ A stable⁺ = Unit
⊥ stable⁺ = Void
(A ∨ B) stable⁺ = Void
⊤ stable⁺ = Void

data SeqForm : Set where
  Rfoc : Type ⁺ → SeqForm
  Inv : Ctx → Conc → SeqForm
  Lfoc : Type ⁻ → Conc → SeqForm

data Exp (א Γ : Ctx) : SeqForm → Set

Value : (א Γ : Ctx) → Type ⁺ → Set
Value א Γ A = Exp א Γ (Rfoc A)

Term : (א Γ : Ctx) → Ctx → Conc → Set
Term א Γ Ω U = Exp א Γ (Inv Ω U)

Spine : (א Γ : Ctx) → Type ⁻ → Conc → Set
Spine א Γ A U = Exp א Γ (Lfoc A U)

data Exp א Γ where

  -- Values
  hyp⁺ : ∀{A}
    (v : A ∈ א)
    → Value א Γ A
  pR : ∀{Q} 
    (x : (a Q ⁺) ∈ Γ)
    → Value א Γ (a Q ⁺) 
  ↓R : ∀{A}
    (N : Term א Γ [] (Reg A))
    → Value א Γ (↓ A)
  ∨R₁ : ∀{A B}
    (V : Value א Γ A)
    → Value א Γ (A ∨ B)
  ∨R₂ : ∀{A B}
    (V : Value א Γ B)
    → Value א Γ (A ∨ B)
  ⊤⁺R : Value א Γ ⊤⁺
  ∧⁺R : ∀{A B}
    (V₁ : Value א Γ A)
    (V₂ : Value א Γ B)
    → Value א Γ (A ∧⁺ B)

  -- Terms
  L : ∀{A Ω U}
    (pf⁺ : A stable⁺)
    (N : Term א (A :: Γ) Ω U)
    → Term א Γ (A :: Ω) U
  ↓L : ∀{A U} 
    (pf⁻ : U stable⁻)
    (x : (↓ A) ∈ Γ)
    (Sp : Spine א Γ A U)
    → Term א Γ [] U
  ⊥L : ∀{U Ω}
    → Term א Γ (⊥ :: Ω) U
  ∨L : ∀{A B Ω U}
    (N₁ : Term א Γ (A :: Ω) U)
    (N₂ : Term א Γ (B :: Ω) U)
    → Term א Γ (A ∨ B :: Ω) U
  ⊤⁺L : ∀{U Ω}
    (N : Term א Γ Ω U)
    → Term א Γ (⊤⁺ :: Ω) U
  ∧⁺L : ∀{U Ω A B}
    (N : Term א Γ (A :: B :: Ω) U)
    → Term א Γ (A ∧⁺ B :: Ω) U
  ↑R : ∀{A} 
    (V : Value א Γ A)
    → Term א Γ [] (Reg (↑ A))
  ⊃R : ∀{A B} 
    (N : Term א Γ [ A ] (Reg B))
    → Term א Γ [] (Reg (A ⊃ B))
  ⊤⁻R : Term א Γ [] (Reg ⊤⁻)
  ∧⁻R : ∀{A B}
    (N₁ : Term א Γ [] (Reg A))
    (N₂ : Term א Γ [] (Reg B))
    → Term א Γ [] (Reg (A ∧⁻ B))

  -- Spines
  hyp⁻ : ∀{A}
    → Spine א Γ A (Abs A)
  pL : ∀{Q}
    → Spine א Γ (a Q ⁻) (Reg (a Q ⁻))
  ↑L : ∀{A U}
    (N : Term א Γ [ A ] U)
    → Spine א Γ (↑ A) U
  ⊃L : ∀{A B U}
    (V : Value א Γ A)
    (Sp : Spine א Γ B U)
    → Spine א Γ (A ⊃ B) U
  ∧⁻L₁ : ∀{A B U}
    (Sp : Spine א Γ A U)
    → Spine א Γ (A ∧⁻ B) U
  ∧⁻L₂ : ∀{A B U}
    (Sp : Spine א Γ B U)
    → Spine א Γ (A ∧⁻ B) U


-- Weakening

wk' : ∀{א א' Γ Γ' Form} → א ⊆ א' → Γ ⊆ Γ' → Exp א Γ Form → Exp א' Γ' Form

wk' ρ θ (hyp⁺ v) = hyp⁺ (ρ v)
wk' ρ θ (pR x) = pR (θ x)
wk' ρ θ (↓R N) = ↓R (wk' ρ θ N)
wk' ρ θ (∨R₁ V) = ∨R₁ (wk' ρ θ V)
wk' ρ θ (∨R₂ V) = ∨R₂ (wk' ρ θ V)
wk' ρ θ ⊤⁺R = ⊤⁺R
wk' ρ θ (∧⁺R V₁ V₂) = ∧⁺R (wk' ρ θ V₁) (wk' ρ θ V₂)

wk' ρ θ (L pf N) = L pf (wk' ρ (LIST.SET.sub-cons-congr θ) N)
wk' ρ θ (↓L pf₁ x Sp) = ↓L pf₁ (θ x) (wk' ρ θ Sp)
wk' ρ θ ⊥L = ⊥L
wk' ρ θ (∨L N₁ N₂) = ∨L (wk' ρ θ N₁) (wk' ρ θ N₂)
wk' ρ θ (⊤⁺L N) = ⊤⁺L (wk' ρ θ N)
wk' ρ θ (∧⁺L N) = ∧⁺L (wk' ρ θ N)
wk' ρ θ (↑R V) = ↑R (wk' ρ θ V)
wk' ρ θ (⊃R N) = ⊃R (wk' ρ θ N)
wk' ρ θ ⊤⁻R = ⊤⁻R
wk' ρ θ (∧⁻R N₁ N₂) = ∧⁻R (wk' ρ θ N₁) (wk' ρ θ N₂)

wk' ρ θ hyp⁻ = hyp⁻
wk' ρ θ pL = pL
wk' ρ θ (↑L N) = ↑L (wk' ρ θ N)
wk' ρ θ (⊃L V Sp) = ⊃L (wk' ρ θ V) (wk' ρ θ Sp)
wk' ρ θ (∧⁻L₁ Sp) = ∧⁻L₁ (wk' ρ θ Sp)
wk' ρ θ (∧⁻L₂ Sp) = ∧⁻L₂ (wk' ρ θ Sp)

wk : ∀{א Γ Γ' Form} → Γ ⊆ Γ' → Exp א Γ Form → Exp א Γ' Form
wk = wk' (λ x → x)

fwk : ∀{א א' Γ Form} → א ⊆ א' → Exp א Γ Form → Exp א' Γ Form
fwk ρ = wk' ρ (λ x → x) 