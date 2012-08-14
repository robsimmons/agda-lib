
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

_⊆_ : ∀{A} → List A → List A → Set
_⊆_ = LIST.SET.Sub


-- Judgmental infrastructure

data Conc : Set where
  Susp : (A : Type ⁻) → Conc
  True : (A : Type ⁺) → Conc
  Inv  : (A : Type ⁻) → Conc

_stableR : Conc → Set
Susp A stableR = Unit
True A stableR = Unit
Inv A stableR = Void

_suspnormalR : Conc → Set
Susp (a Q .⁻) suspnormalR = Unit
Susp (↑ A) suspnormalR = Void
Susp (A ⊃ B) suspnormalR = Void
Susp ⊤⁻ suspnormalR = Void
Susp (A ∧⁻ B) suspnormalR = Void
True A suspnormalR = Unit
Inv A suspnormalR = Unit

_suspstable : Conc → Set
U suspstable = U stableR × U suspnormalR

data Hyp : Set where
  Susp : (A : Type ⁺) → Hyp
  Pers : (A : Type ⁻) → Hyp

Ctx = List Hyp

_suspnormalL : Hyp → Set
Susp (a Q .⁺) suspnormalL = Unit
Susp (↓ A) suspnormalL = Void
Susp ⊥ suspnormalL = Void
Susp (A ∨ B) suspnormalL = Void
Susp ⊤⁺ suspnormalL = Void
Susp (A ∧⁺ B) suspnormalL = Void
Pers A suspnormalL = Unit

_suspnormalΓ : Ctx → Set
Γ suspnormalΓ = ∀{H} → H ∈ Γ → H suspnormalL 

cons : ∀{Γ H} → H suspnormalL → Γ suspnormalΓ → (H :: Γ) suspnormalΓ
cons pf pfΓ Z = pf
cons pf pfΓ (S n) = pfΓ n

fromctx : ∀{A B Γ} (Γ' : Ctx) → B ∈ (Γ' ++ A :: Γ) → (A ≡ B) + (B ∈ (Γ' ++ Γ))
fromctx [] Z = Inl Refl
fromctx [] (S x) = Inr x
fromctx (A :: Γ') Z = Inr Z
fromctx (A :: Γ') (S x) with fromctx Γ' x
... | Inl Refl = Inl Refl
... | Inr x' = Inr (S x')


-- Sequent calculus

data SeqForm : Set where
  Rfoc : (A : Type ⁺) → SeqForm
  Left : (L : List (Type ⁺) + Type ⁻) (U : Conc) → SeqForm 

_suspnormalF : SeqForm → Set
Rfoc A suspnormalF = Unit
Left L U suspnormalF = U suspnormalR

data Exp (Γ : Ctx) : SeqForm → Set

Value : (Γ : Ctx) → Type ⁺ → Set
Value Γ A = Exp Γ (Rfoc A)

Term : (Γ : Ctx) → List (Type ⁺) → Conc → Set
Term Γ Ω U = Exp Γ (Left (Inl Ω) U)

Spine : (Γ : Ctx) (A : Type ⁻) (U : Conc) → Set
Spine Γ A U = Exp Γ (Left (Inr A) U)

data Exp Γ where

  -- Values
  id⁺ : ∀{A}
    (v : Susp A ∈ Γ)
    → Value Γ A

  ↓R : ∀{A}
    (N : Term Γ [] (Inv A))
    → Value Γ (↓ A)
  ∨R₁ : ∀{A B}
    (V : Value Γ A)
    → Value Γ (A ∨ B)
  ∨R₂ : ∀{A B}
    (V : Value Γ B)
    → Value Γ (A ∨ B)
  ⊤⁺R : Value Γ ⊤⁺
  ∧⁺R : ∀{A B}
    (V₁ : Value Γ A)
    (V₂ : Value Γ B)
    → Value Γ (A ∧⁺ B)

  -- Terms
  focusR : ∀{A} 
    (V : Value Γ A)
    → Term Γ [] (True A)
  focusL : ∀{A U} 
    (pf : U stableR)
    (x : Pers A ∈ Γ)
    (Sp : Spine Γ A U)
    → Term Γ [] U
  η⁺ : ∀{Q Ω U}
    (N : Term (Susp (a Q ⁺) :: Γ) Ω U)
    → Term Γ (a Q ⁺ :: Ω) U
  η⁻ : ∀{Q}
    (N : Term Γ [] (Susp (a Q ⁻)))
    → Term Γ [] (Inv (a Q ⁻))

  ↓L : ∀{A Ω U}
    (N : Term (Pers A :: Γ) Ω U)
    → Term Γ (↓ A :: Ω) U
  ↑R : ∀{A} 
    (N : Term Γ [] (True A))
    → Term Γ [] (Inv (↑ A)) 
  ⊥L : ∀{U Ω}
    → Term Γ (⊥ :: Ω) U
  ∨L : ∀{A B Ω U}
    (N₁ : Term Γ (A :: Ω) U)
    (N₂ : Term Γ (B :: Ω) U)
    → Term Γ (A ∨ B :: Ω) U
  ⊤⁺L : ∀{U Ω}
    (N : Term Γ Ω U)
    → Term Γ (⊤⁺ :: Ω) U
  ∧⁺L : ∀{U Ω A B}
    (N : Term Γ (A :: B :: Ω) U)
    → Term Γ (A ∧⁺ B :: Ω) U
  ⊃R : ∀{A B} 
    (N : Term Γ [ A ] (Inv B))
    → Term Γ [] (Inv (A ⊃ B))
  ⊤⁻R : Term Γ [] (Inv ⊤⁻)
  ∧⁻R : ∀{A B}
    (N₁ : Term Γ [] (Inv A))
    (N₂ : Term Γ [] (Inv B))
    → Term Γ [] (Inv (A ∧⁻ B))

  -- Spines
  id⁻ : ∀{A}
    → Spine Γ A (Susp A)

  ↑L : ∀{A U}
    (N : Term Γ [ A ] U)
    → Spine Γ (↑ A) U
  ⊃L : ∀{A B U}
    (V : Value Γ A)
    (Sp : Spine Γ B U) 
    → Spine Γ (A ⊃ B) U
  ∧⁻L₁ : ∀{A B U}
    (Sp : Spine Γ A U)
    → Spine Γ (A ∧⁻ B) U
  ∧⁻L₂ : ∀{A B U}
    (Sp : Spine Γ B U)
    → Spine Γ (A ∧⁻ B) U


-- Weakening

wk : ∀{Γ Γ' Form} → Γ ⊆ Γ' → Exp Γ Form → Exp Γ' Form

wk θ (id⁺ v) = id⁺ (θ v)
wk θ (↓R N) = ↓R (wk θ N)
wk θ (∨R₁ V) = ∨R₁ (wk θ V)
wk θ (∨R₂ V) = ∨R₂ (wk θ V)
wk θ ⊤⁺R = ⊤⁺R
wk θ (∧⁺R V₁ V₂) = ∧⁺R (wk θ V₁) (wk θ V₂)

wk θ (focusR V) = focusR (wk θ V)
wk θ (focusL pf x Sp) = focusL pf (θ x) (wk θ Sp)
wk θ (η⁺ N) = η⁺ (wk (LIST.SET.sub-cons-congr θ) N)
wk θ (η⁻ N) = η⁻ (wk θ N)
wk θ (↓L N) = ↓L (wk (LIST.SET.sub-cons-congr θ) N)
wk θ (↑R N) = ↑R (wk θ N)
wk θ ⊥L = ⊥L
wk θ (∨L N₁ N₂) = ∨L (wk θ N₁) (wk θ N₂)
wk θ (⊤⁺L N) = ⊤⁺L (wk θ N)
wk θ (∧⁺L N) = ∧⁺L (wk θ N)
wk θ (⊃R N) = ⊃R (wk θ N)
wk θ ⊤⁻R = ⊤⁻R
wk θ (∧⁻R N₁ N₂) = ∧⁻R (wk θ N₁) (wk θ N₂)

wk θ id⁻ = id⁻
wk θ (↑L N) = ↑L (wk θ N)
wk θ (⊃L V Sp) = ⊃L (wk θ V) (wk θ Sp)
wk θ (∧⁻L₁ Sp) = ∧⁻L₁ (wk θ Sp)
wk θ (∧⁻L₂ Sp) = ∧⁻L₂ (wk θ Sp)

wken : ∀{Γ A Form} → Exp Γ Form → Exp (A :: Γ) Form
wken = wk LIST.SET.sub-wken

