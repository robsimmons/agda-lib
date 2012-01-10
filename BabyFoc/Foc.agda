open import Prelude hiding (⊥; ⊤)

module BabyFoc.Foc where

-- Propositions and polarity

data Polarity : Set where
  ⁺ : Polarity
  ⁻ : Polarity

data Type : Set where
  a : (Q : String) (⁼ : Polarity) → Type
  ⊥ : Type
  _∨_ : (A B : Type) → Type
  ⊤ : Type
  _⊃_ : (A B : Type) → Type

_neg : Type → Set
a Q ⁺ neg = Void
⊥ neg = Void
(A ∨ B) neg = Void
⊤ neg = Void
a Q ⁻ neg = Unit
(A ⊃ B) neg = Unit

_pos : Type → Set
a Q ⁺ pos = Unit
⊥ pos = Unit
(A ∨ B) pos = Unit
⊤ pos = Unit
a Q ⁻ pos = Void
(A ⊃ B) pos = Void

Ctx = List Type

_⊆_ : Ctx → Ctx → Set
_⊆_ = LIST.SET.Sub


-- Sequent calculus

data Conc : Set where
  Abs : (A : Type) → Conc
  Reg : (A : Type) → Conc

_stable : Conc → Set
Abs A stable = Unit
Reg (a Q ⁺) stable = Unit
Reg (a Q ⁻) stable = Unit
Reg (A ⊃ B) stable = Void
Reg ⊥ stable = Unit
Reg (A ∨ B) stable = Unit
Reg ⊤ stable = Unit

data Value (א Γ : Ctx) : Type → Set
data Term (א Γ : Ctx) : Conc → Set
data Spine (א Γ : Ctx) : Type → Conc → Set

data Value א Γ where
  hyp⁺ : ∀{A}
    (v : A ∈ א)
    → Value א Γ A
  pR : ∀{Q} 
    (x : (a Q ⁺) ∈ Γ)
    → Value א Γ (a Q ⁺) 
  ↓R : ∀{A}
    (pf : A neg)
    (N : Term א Γ (Reg A))
    → Value א Γ A
  ∨R₁ : ∀{A B}
    (V : Value א Γ A)
    → Value א Γ (A ∨ B)
  ∨R₂ : ∀{A B}
    (V : Value א Γ B)
    → Value א Γ (A ∨ B)
  ⊤R : Value א Γ ⊤
  
data Term א Γ where
  foc : ∀{A U} 
    (pf₁ : U stable)
    (x : A ∈ Γ)
    (pf₂ : A neg)
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
  rfoc : ∀{A} 
    (pf : A pos)
    (V : Value א Γ A)
    → Term א Γ (Reg A)
  ⊃R : ∀{A B} 
    (N : Term א (A :: Γ) (Reg B))
    → Term א Γ (Reg (A ⊃ B))

data Spine א Γ where
  hyp⁻ : ∀{A}
    → Spine א Γ A (Abs A)
  pL : ∀{Q}
    → Spine א Γ (a Q ⁻) (Reg (a Q ⁻))
  ↑L : ∀{A U}
    (pf : A pos)
    (N : Term א (A :: Γ) U)
    → Spine א Γ A U
  ⊃L : ∀{A B U}
    (V : Value א Γ A)
    (Sp : Spine א Γ B U)
    → Spine א Γ (A ⊃ B) U


-- Weakening

wkV' : ∀{א א' Γ Γ' A} → א ⊆ א' → Γ ⊆ Γ' → Value א Γ A → Value א' Γ' A
wkN' : ∀{א א' Γ Γ' U} → א ⊆ א' → Γ ⊆ Γ' → Term א Γ U → Term א' Γ' U
wkSp' : ∀{א א' Γ Γ' A U} → א ⊆ א' → Γ ⊆ Γ' → Spine א Γ A U → Spine א' Γ' A U

wkV' ρ θ (hyp⁺ v) = hyp⁺ (ρ v)
wkV' ρ θ (pR x) = pR (θ x)
wkV' ρ θ (↓R pf N) = ↓R pf (wkN' ρ θ N)
wkV' ρ θ (∨R₁ V) = ∨R₁ (wkV' ρ θ V)
wkV' ρ θ (∨R₂ V) = ∨R₂ (wkV' ρ θ V)
wkV' ρ θ ⊤R = ⊤R

wkN' ρ θ (foc pf₁ x pf₂ Sp) = foc pf₁ (θ x) pf₂ (wkSp' ρ θ Sp)
wkN' ρ θ (⊥L x) = ⊥L (θ x)
wkN' ρ θ (∨L x N₁ N₂) = 
  ∨L (θ x) (wkN' ρ (LIST.SET.sub-cons-congr θ) N₁) 
    (wkN' ρ (LIST.SET.sub-cons-congr θ) N₂)
wkN' ρ θ (⊤L x N) = ⊤L (θ x) (wkN' ρ θ N)
wkN' ρ θ (rfoc pf V) = rfoc pf (wkV' ρ θ V)
wkN' ρ θ (⊃R N) = ⊃R (wkN' ρ (LIST.SET.sub-cons-congr θ) N)

wkSp' ρ θ hyp⁻ = hyp⁻
wkSp' ρ θ pL = pL
wkSp' ρ θ (↑L pf N) = ↑L pf (wkN' ρ (LIST.SET.sub-cons-congr θ) N)
wkSp' ρ θ (⊃L V Sp) = ⊃L (wkV' ρ θ V) (wkSp' ρ θ Sp)

wkV : ∀{א Γ Γ' A} → Γ ⊆ Γ' → Value א Γ A → Value א Γ' A
wkV = wkV' (λ x → x)

wkN : ∀{א Γ Γ' U} → Γ ⊆ Γ' → Term א Γ U → Term א Γ' U
wkN = wkN' (λ x → x)

wkSp : ∀{א Γ Γ' A U} → Γ ⊆ Γ' → Spine א Γ A U → Spine א Γ' A U
wkSp = wkSp' (λ x → x)
