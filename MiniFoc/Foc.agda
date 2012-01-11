open import Prelude hiding (⊥; ⊤)

module MiniFoc.Foc where

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
  ⊤ : Type ⁺
  --
  ↑ : (A : Type ⁺) → Type ⁻
  _⊃_ : (A : Type ⁺) (B : Type ⁻) → Type ⁻

Ctx = List (Type ⁺)

_⊆_ : Ctx → Ctx → Set
_⊆_ = LIST.SET.Sub



-- Sequent calculus

data Conc : Set where
  Abs : (A : Type ⁻) → Conc
  Reg : (A : Type ⁻) → Conc

_stable : Conc → Set
Abs A stable = Unit
Reg (a Q .⁻) stable = Unit
Reg (↑ A) stable = Unit
Reg (A ⊃ B) stable = Void


data SeqForm : Set where
  Rfoc : Type ⁺ → SeqForm
  Inv : Conc → SeqForm
  Lfoc : Type ⁻ → Conc → SeqForm

data Exp (א Γ : Ctx) : SeqForm → Set

Value : (א Γ : Ctx) → Type ⁺ → Set
Value א Γ A = Exp א Γ (Rfoc A)

Term : (א Γ : Ctx) → Conc → Set
Term א Γ U = Exp א Γ (Inv U)

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
    (N : Term א Γ (Reg A))
    → Value א Γ (↓ A)
  ∨R₁ : ∀{A B}
    (V : Value א Γ A)
    → Value א Γ (A ∨ B)
  ∨R₂ : ∀{A B}
    (V : Value א Γ B)
    → Value א Γ (A ∨ B)
  ⊤R : Value א Γ ⊤

  -- Terms
  ↓L : ∀{A U} 
    (pf₁ : U stable)
    (x : (↓ A) ∈ Γ)
    (Sp : Spine א Γ A U)
    → Term א Γ U
  ⊥L : ∀{U}
    (x : ⊥ ∈ Γ)
    → Term א Γ U
  ∨L : ∀{A B U}
    (x : A ∨ B ∈ Γ)
    (N₁ : Term א (A :: Γ) U)
    (N₂ : Term א (B :: Γ) U)
    → Term א Γ U
  ⊤L : ∀{U}
    (x : ⊤ ∈ Γ)
    (N : Term א Γ U)
    → Term א Γ U
  ↑R : ∀{A} 
    (V : Value א Γ A)
    → Term א Γ (Reg (↑ A))
  ⊃R : ∀{A B} 
    (N : Term א (A :: Γ) (Reg B))
    → Term א Γ (Reg (A ⊃ B))

  -- Spines
  hyp⁻ : ∀{A}
    → Spine א Γ A (Abs A)
  pL : ∀{Q}
    → Spine א Γ (a Q ⁻) (Reg (a Q ⁻))
  ↑L : ∀{A U}
    (N : Term א (A :: Γ) U)
    → Spine א Γ (↑ A) U
  ⊃L : ∀{A B U}
    (V : Value א Γ A)
    (Sp : Spine א Γ B U)
    → Spine א Γ (A ⊃ B) U


-- Weakening

wk' : ∀{א א' Γ Γ' Form} → א ⊆ א' → Γ ⊆ Γ' → Exp א Γ Form → Exp א' Γ' Form

wk' ρ θ (hyp⁺ v) = hyp⁺ (ρ v)
wk' ρ θ (pR x) = pR (θ x)
wk' ρ θ (↓R N) = ↓R (wk' ρ θ N)
wk' ρ θ (∨R₁ V) = ∨R₁ (wk' ρ θ V)
wk' ρ θ (∨R₂ V) = ∨R₂ (wk' ρ θ V)
wk' ρ θ ⊤R = ⊤R

wk' ρ θ (↓L pf₁ x Sp) = ↓L pf₁ (θ x) (wk' ρ θ Sp)
wk' ρ θ (⊥L x) = ⊥L (θ x)
wk' ρ θ (∨L x N₁ N₂) = 
  ∨L (θ x) (wk' ρ (LIST.SET.sub-cons-congr θ) N₁) 
    (wk' ρ (LIST.SET.sub-cons-congr θ) N₂)
wk' ρ θ (⊤L x N) = ⊤L (θ x) (wk' ρ θ N)
wk' ρ θ (↑R V) = ↑R (wk' ρ θ V)
wk' ρ θ (⊃R N) = ⊃R (wk' ρ (LIST.SET.sub-cons-congr θ) N)

wk' ρ θ hyp⁻ = hyp⁻
wk' ρ θ pL = pL
wk' ρ θ (↑L N) = ↑L (wk' ρ (LIST.SET.sub-cons-congr θ) N)
wk' ρ θ (⊃L V Sp) = ⊃L (wk' ρ θ V) (wk' ρ θ Sp)

wk : ∀{א Γ Γ' Form} → Γ ⊆ Γ' → Exp א Γ Form → Exp א Γ' Form
wk = wk' (λ x → x)

