open import Prelude hiding (⊥; ⊤)

module BabyFoc.Foc where

data Polarity : Set where
  ⁺ : Polarity
  ⁻ : Polarity

data Type : Set where
  a : (Q : String) (⁼ : Polarity) → Type
  _⊃_ : (A : Type) (B : Type) → Type
  ⊥ : Type
  ⊤ : Type

_neg : Type → Set
a Q ⁺ neg = Void
a Q ⁻ neg = Unit
(A ⊃ B) neg = Unit
⊥ neg = Void
⊤ neg = Void

_pos : Type → Set
A pos = ¬ (A neg)

Ctx = List Type

_⊆_ : Ctx → Ctx → Set
_⊆_ = LIST.SET.Sub


data Conc : Set where
  Abs : (A : Type) → Conc
  Reg : (A : Type) → Conc

_stable : Conc → Set
Abs A stable = Unit
Reg (a Q ⁺) stable = Unit
Reg (a Q ⁻) stable = Unit
Reg (A ⊃ B) stable = Void
Reg ⊥ stable = Unit
Reg ⊤ stable = Unit

data _⊢_foc (Γ : Ctx) : Type → Set
data _⊢_inv (Γ : Ctx) : Conc → Set
data _⊢_>_ (Γ : Ctx) : Type → Conc → Set

data _⊢_foc Γ where
  pR : ∀{Q} 
    (x : (a Q ⁺) ∈ Γ)
    → Γ ⊢ (a Q ⁺) foc
  ↓R : ∀{A}
    (pf : A neg)
    (N : Γ ⊢ Reg A inv)
    → Γ ⊢ A foc
  ⊤R : Γ ⊢ ⊤ foc
  
data _⊢_inv Γ where
  foc : ∀{A U} 
    (pf₁ : U stable)
    (x : A ∈ Γ)
    (pf₂ : A neg)
    (Sp : Γ ⊢ A > U)
    → Γ ⊢ U inv
  rfoc : ∀{A} 
    (pf : A pos)
    (V : Γ ⊢ A foc)
    → Γ ⊢ Reg A inv
  ⊃R : ∀{A B} 
    (N : (A :: Γ) ⊢ Reg B inv)
    → Γ ⊢ Reg (A ⊃ B) inv
  ⊥L : ∀{U}
    (x : ⊥ ∈ Γ)
    → Γ ⊢ U inv

data _⊢_>_ Γ where
  hyp : ∀{A}
    → Γ ⊢ A > Abs A
  pL : ∀{Q}
    → Γ ⊢ (a Q ⁻) > Reg (a Q ⁻)
  ↑L : ∀{A U}
    (pf : A pos)
    (N : (A :: Γ) ⊢ U inv)
    → Γ ⊢ A > U
  ⊃L : ∀{A B U}
    (V : Γ ⊢ A foc)
    (Sp : Γ ⊢ B > U)
    → Γ ⊢ A ⊃ B > U


wkV : ∀{Γ Γ' A} → Γ ⊆ Γ' → Γ ⊢ A foc → Γ' ⊢ A foc
wkN : ∀{Γ Γ' U} → Γ ⊆ Γ' → Γ ⊢ U inv → Γ' ⊢ U inv
wkSp : ∀{Γ Γ' A U} → Γ ⊆ Γ' → Γ ⊢ A > U → Γ' ⊢ A > U

wkV θ (pR x) = pR (θ x)
wkV θ (↓R pf N) = ↓R pf (wkN θ N)
wkV θ ⊤R = ⊤R

wkN θ (foc pf₁ x pf₂ Sp) = foc pf₁ (θ x) pf₂ (wkSp θ Sp)
wkN θ (⊃R N) = ⊃R (wkN (LIST.SET.sub-cons-congr θ) N)
wkN θ (rfoc pf V) = rfoc pf (wkV θ V)
wkN θ (⊥L x) = ⊥L (θ x)

wkSp θ hyp = hyp
wkSp θ pL = pL
wkSp θ (↑L pf N) = ↑L pf (wkN (LIST.SET.sub-cons-congr θ) N)
wkSp θ (⊃L V Sp) = ⊃L (wkV θ V) (wkSp θ Sp)

<<>> : Void → Void
<<>> x = x