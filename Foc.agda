
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
  Inv  : (A : Type ⁻) → Conc
  True : (A : Type ⁺) → Conc
  Susp : (A : Type ⁻) → Conc

stable : Conc → Set
stable (Inv A) = Void
stable (True A) = Unit
stable (Susp A) = Unit

suspnormal : Conc → Set
suspnormal (Inv A) = Unit
suspnormal (True A) = Unit
suspnormal (Susp (a Q .⁻)) = Unit
suspnormal (Susp (↑ A)) = Void
suspnormal (Susp (A ⊃ A₁)) = Void
suspnormal (Susp ⊤⁻) = Void
suspnormal (Susp (A ∧⁻ A₁)) = Void

suspstable : Conc -> Set
suspstable U = stable U × suspnormal U

data Hyp : Set where
  Susp : (A : Type ⁺) → Hyp
  Pers : (A : Type ⁻) → Hyp

Ctx = List Hyp

{- Suspension normality: all suspended propositions are atomic -}
suspnormalΓ : Ctx → Set
suspnormalΓ Γ = ∀{A} → Susp A ∈ Γ → ∃ λ Q → Id A (a Q ⁺)

{-

_suspnormalL : Hyp → Set
Susp (a Q .⁺) suspnormalL = Unit
Susp (↓ A) suspnormalL = Void
Susp ⊥ suspnormalL = Void
Susp (A ∨ B) suspnormalL = Void
Susp ⊤⁺ suspnormalL = Void
Susp (A ∧⁺ B) suspnormalL = Void
Pers A suspnormalL = Unit


cons : ∀{Γ H} → H suspnormalL → Γ suspnormalΓ → (H :: Γ) suspnormalΓ
cons pf pfΓ Z = pf
cons pf pfΓ (S n) = pfΓ n
-}

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

suspnormalF : SeqForm → Set
suspnormalF (Rfoc A) = Unit
suspnormalF (Left L U) = suspnormal U

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
  focR : ∀{A} 
    (V : Value Γ A)
    → Term Γ [] (True A)
  focL : ∀{A U} 
    (pf : stable U)
    (x : Pers A ∈ Γ)
    (Sp : Spine Γ A U)
    → Term Γ [] U
  η⁺ : ∀{Q Ω U}
    (N : Term (Susp (a Q ⁺) :: Γ) Ω U)
    → Term Γ (a Q ⁺ :: Ω) U
  ↓L : ∀{A Ω U}
    (N : Term (Pers A :: Γ) Ω U)
    → Term Γ (↓ A :: Ω) U
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
  η⁻ : ∀{Q}
    (N : Term Γ [] (Susp (a Q ⁻)))
    → Term Γ [] (Inv (a Q ⁻))
  ↑R : ∀{A} 
    (N : Term Γ [] (True A))
    → Term Γ [] (Inv (↑ A)) 
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

wk θ (focR V) = focR (wk θ V)
wk θ (focL pf x Sp) = focL pf (θ x) (wk θ Sp)
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



-- Focal substitution

-- Values substituted in for suspended positive propositions

subst⁺ : ∀{Γ A Form} (Γ' : Ctx)
  → Value (Γ' ++ Γ) A
  → Exp (Γ' ++ Susp A :: Γ) Form
  → Exp (Γ' ++ Γ) Form

subst⁺ Γ' V (id⁺ x) with fromctx Γ' x
... | Inl Refl = V
... | Inr x' = id⁺ x'
subst⁺ Γ' V (↓R N) = ↓R (subst⁺ Γ' V N)
subst⁺ Γ' V (∨R₁ V') = ∨R₁ (subst⁺ Γ' V V')
subst⁺ Γ' V (∨R₂ V') = ∨R₂ (subst⁺ Γ' V V')
subst⁺ Γ' V ⊤⁺R = ⊤⁺R
subst⁺ Γ' V (∧⁺R V₁ V₂) = ∧⁺R (subst⁺ Γ' V V₁) (subst⁺ Γ' V V₂)

subst⁺ Γ' V (focR V') = focR (subst⁺ Γ' V V')
subst⁺ Γ' V (focL pf x Sp) with fromctx Γ' x
... | Inl ()
... | Inr x' = focL pf x' (subst⁺ Γ' V Sp)
subst⁺ Γ' V (η⁺ N) = η⁺ (subst⁺ (_ :: Γ') (wken V) N)
subst⁺ Γ' V (η⁻ N) = η⁻ (subst⁺ Γ' V N)
subst⁺ Γ' V (↓L N) = ↓L (subst⁺ (_ :: Γ') (wken V) N)
subst⁺ Γ' V (↑R N) = ↑R (subst⁺ Γ' V N)
subst⁺ Γ' V ⊥L = ⊥L
subst⁺ Γ' V (∨L N₁ N₂) = ∨L (subst⁺ Γ' V N₁) (subst⁺ Γ' V N₂)
subst⁺ Γ' V (⊤⁺L N) = ⊤⁺L (subst⁺ Γ' V N)
subst⁺ Γ' V (∧⁺L N) = ∧⁺L (subst⁺ Γ' V N)
subst⁺ Γ' V (⊃R N) = ⊃R (subst⁺ Γ' V N)
subst⁺ Γ' V ⊤⁻R = ⊤⁻R
subst⁺ Γ' V (∧⁻R N₁ N₂) = ∧⁻R (subst⁺ Γ' V N₁) (subst⁺ Γ' V N₂)

subst⁺ Γ' V id⁻ = id⁻
subst⁺ Γ' V (↑L N) = ↑L (subst⁺ Γ' V N)
subst⁺ Γ' V (⊃L V' Sp) = ⊃L (subst⁺ Γ' V V') (subst⁺ Γ' V Sp)
subst⁺ Γ' V (∧⁻L₁ Sp) = ∧⁻L₁ (subst⁺ Γ' V Sp)
subst⁺ Γ' V (∧⁻L₂ Sp) = ∧⁻L₂ (subst⁺ Γ' V Sp)

-- Spines substituted out for suspended negative propositions

subst⁻ : ∀{Γ A L U}
  → stable U
  → Exp Γ (Left L (Susp A))
  → Spine Γ A U
  → Exp Γ (Left L U)

subst⁻ pf (focL _ x Sp) Sp' = focL pf x (subst⁻ pf Sp Sp')
subst⁻ pf (η⁺ N) Sp = η⁺ (subst⁻ pf N (wken Sp))
subst⁻ pf (↓L N) Sp = ↓L (subst⁻ pf N (wken Sp))
subst⁻ pf ⊥L Sp = ⊥L
subst⁻ pf (∨L N₁ N₂) Sp = ∨L (subst⁻ pf N₁ Sp) (subst⁻ pf N₂ Sp)
subst⁻ pf (⊤⁺L N) Sp = ⊤⁺L (subst⁻ pf N Sp)
subst⁻ pf (∧⁺L N) Sp = ∧⁺L (subst⁻ pf N Sp)

subst⁻ pf id⁻ Sp = Sp
subst⁻ pf (↑L N) Sp = ↑L (subst⁻ pf N Sp)
subst⁻ pf (⊃L V Sp) Sp' = ⊃L V (subst⁻ pf Sp Sp')
subst⁻ pf (∧⁻L₁ Sp) Sp' = ∧⁻L₁ (subst⁻ pf Sp Sp')
subst⁻ pf (∧⁻L₂ Sp) Sp' = ∧⁻L₂ (subst⁻ pf Sp Sp')

