
open import Prelude hiding (⊥)

module AltPolar where


-- Types
data Polarity : Set where
  ⁺ : Polarity
  ⁻ : Polarity

data Type : Polarity → Set where
   a : (Q : String) (⁼ : Polarity) → Type ⁼
   _∧⁺_ : (A B : Type ⁺) → Type ⁺
   ⊤⁺ : Type ⁺
   _∨_ : (A B : Type ⁺) → Type ⁺
   ⊥ : Type ⁺
   _∧⁻_ : (A B : Type ⁻) → Type ⁻
   ⊤⁻ : Type ⁻
   _⊃_ : (A : Type ⁺) (B : Type ⁻) → Type ⁻
   ↓ : (A : Type ⁻) → Type ⁺
   ↑ : (A : Type ⁺) → Type ⁻


-- Contexts
data Hyp : Set where
  ⟨_⟩ : (A : Type ⁻) → Hyp
  ⟨⟨_⟩⟩ : (A : Type ⁺) → Hyp

Ctx = List Hyp

_⊆_ : ∀{A} → List A → List A → Set
_⊆_ = LIST.SET.Sub

data Conc : Set where
  ⟨_⟩ : (A : Type ⁺) → Conc
  ⟨⟨_⟩⟩ : (A : Type ⁻) → Conc


-- Interpretation of types
I⁺ : Type ⁺ → (Ctx → Set) → (Ctx → Set)
I⁺ (a Q .⁺) P = λ Γ → P (⟨⟨ a Q ⁺ ⟩⟩ :: Γ)
I⁺ (A ∧⁺ B) P = I⁺ A (I⁺ B P)
I⁺ ⊤⁺ P = P
I⁺ (A ∨ B) P = λ Γ → I⁺ A P Γ × I⁺ B P Γ
I⁺ ⊥ P = λ Γ → ⊤
I⁺ (↓ A) P = λ Γ → P (⟨ A ⟩ :: Γ)

I⁻ : Type ⁻ → (Conc → Ctx → Set) → (Ctx → Set)
I⁻ (a Q .⁻) P = P ⟨⟨ a Q ⁻ ⟩⟩
I⁻ (A ∧⁻ B) P = λ Γ → I⁻ A P Γ × I⁻ B P Γ
I⁻ ⊤⁻ P = λ Γ → ⊤
I⁻ (A ⊃ B) P = I⁺ A (I⁻ B P)
I⁻ (↑ A) P = P ⟨ A ⟩ -- P [] ⟨ A ⟩


-- Sequents
data SeqForm : Set where
  Rfoc : Type ⁺ → SeqForm
  Prove : Conc → SeqForm
  Lfoc : Type ⁻ → Conc → SeqForm

data Exp (Γ : Ctx) : SeqForm → Set

Value : (Γ : Ctx) → Type ⁺ → Set
Value Γ A = Exp Γ (Rfoc A)

Term : (Γ : Ctx) → Conc → Set
Term Γ U = Exp Γ (Prove U)

Spine : (Γ : Ctx) → Type ⁻ → Conc → Set
Spine Γ A U = Exp Γ (Lfoc A U)

Inv⁺ : (Γ : Ctx) → Type ⁺ → Conc → Set
Inv⁺ Γ A U = I⁺ A (λ Γ' → Term Γ' U) Γ

Inv⁻ : (Γ : Ctx) → Type ⁻ → Set 
Inv⁻ Γ A = I⁻ A (λ U Γ' → Term Γ' U) Γ

data Exp Γ where

  -- Values
  id⁺ : ∀{A}
    (x : ⟨⟨ A ⟩⟩ ∈ Γ)
    → Value Γ A
  ↓R : ∀{A}
    (N : Inv⁻ Γ A)
    → Value Γ (↓ A)
  ⊤⁺R : Value Γ ⊤⁺
  ∧⁺R : ∀{A B}
    (V₁ : Value Γ A)
    (V₂ : Value Γ B)
    → Value Γ (A ∧⁺ B)
  ∨R₁ : ∀{A B}
    (V : Value Γ A)
    → Value Γ (A ∨ B)
  ∨R₂ : ∀{A B}
    (V : Value Γ B)
    → Value Γ (A ∨ B)

  -- Terms
  rfoc : ∀{A}
    (V : Value Γ A)
    → Term Γ ⟨ A ⟩ 
  lfoc : ∀{A U}
    (x : ⟨ A ⟩ ∈ Γ)
    (Sp : Spine Γ A U)
    → Term Γ U
  
  -- Spines
  id⁻ : ∀{A}
    → Spine Γ A ⟨⟨ A ⟩⟩
  ↑L : ∀{A U}
    (N : Inv⁺ Γ A U)
    → Spine Γ (↑ A) U
  ∧⁻L₁ : ∀{A B U}
    (Sp : Spine Γ A U)
    → Spine Γ (A ∧⁻ B) U
  ∧⁻L₂ : ∀{A B U}
    (Sp : Spine Γ B U)
    → Spine Γ (A ∧⁻ B) U
  ⊃L : ∀{A B U}
    (V : Value Γ A)
    (Sp : Spine Γ B U)
    → Spine Γ (A ⊃ B) U

wk : ∀{Γ Γ' J} → Γ ⊆ Γ' → Exp Γ J → Exp Γ' J
wk θ E = {!!}

record Props⁺ (P : Ctx → Set) : Set where 
 field
  wk⁺ : ∀{Γ Γ'} → Γ ⊆ Γ' → P Γ → P Γ'
open Props⁺ public

record Props⁻ (P : Conc → Ctx → Set) : Set where 
 field
  wk⁻ : ∀{Γ Γ' J} → Γ ⊆ Γ' → P J Γ → P J Γ'
open Props⁻ public

fmap⁺ : {P : Ctx → Set} {P' : Ctx → Set} 
  → (A : Type ⁺)
  → (∀{Γ Γ'} → Γ ⊆ Γ' → P Γ → P' Γ') 
  → (∀{Γ Γ'} → Γ ⊆ Γ' → I⁺ A P Γ → I⁺ A P' Γ')
fmap⁺ (a Q .⁺) f θ N = f (LIST.SET.sub-cons-congr θ) N
fmap⁺ (A ∧⁺ B) f θ N = fmap⁺ A (fmap⁺ B f) θ N 
fmap⁺ ⊤⁺ f θ N = f θ N 
fmap⁺ (A ∨ B) f θ (N₁ , N₂) = fmap⁺ A f θ N₁ , fmap⁺ B f θ N₂
fmap⁺ ⊥ f θ <> = <> 
fmap⁺ (↓ A) f θ N = f (LIST.SET.sub-cons-congr θ) N

cut⁺ : ∀{Γ} (A : Type ⁺) {P : Ctx → Set}
  → Props⁺ P
  → I⁺ A P Γ
  → ({Γ' : Ctx} (V : Value Γ' A) (θ : Γ ⊆ Γ') → P Γ') 

cut⁻ : ∀{Γ} (A : Type ⁻) {P : Conc → Ctx → Set}
  → Props⁻ P
  → I⁻ A P Γ
  → ({U : Conc} {Γ' : Ctx} (Sp : Spine Γ' A U) (θ : Γ ⊆ Γ') → P U Γ')

cut⁺ {Γ} (a Q .⁺) {P} pr N {Γ'} (id⁺ x) θ = wk⁺ pr θ' N
 where
  θ' : ∀{H} → H ∈ (⟨⟨ a Q ⁺ ⟩⟩ :: Γ) → H ∈ Γ' 
  θ' Z = x
  θ' (S n) = θ n

cut⁺ {Γ} A {P} pr N {Γ'} (id⁺ x) θ = {!!} -- excluded

cut⁺ (A ∧⁺ B) pr N (∧⁺R V₁ V₂) θ =  
  cut⁺ A pr 
    (fmap⁺ A (λ θ' N' → cut⁺ B pr N' (wk {!θ!} V₂) θ') (λ x → x) N) 
    V₁ θ
cut⁺ ⊤⁺ pr N ⊤⁺R θ = wk⁺ pr θ N
cut⁺ (A ∨ B) pr (N₁ , N₂) (∨R₁ V) θ = {!!}
cut⁺ (A ∨ B) pr (N₁ , N₂) (∨R₂ V) θ = {!!}
cut⁺ (↓ A) pr N V θ = {!!}

cut⁻ A pr N Sp θ = {!!}


expand⁺ : ∀{Γ} (A : Type ⁺) {P : Ctx → Set}
  → ({Γ' : Ctx} (V : Value Γ' A) (θ : Γ ⊆ Γ') → P Γ') 
  → I⁺ A P Γ

expand⁻ : ∀{Γ} (A : Type ⁻) {P : Conc → Ctx → Set}
  → ({U : Conc} {Γ' : Ctx} (Sp : Spine Γ' A U) (θ : Γ ⊆ Γ') → P U Γ')
  → I⁻ A P Γ

expand⁺ (a Q .⁺) F = F (id⁺ Z) LIST.SET.sub-wken 
expand⁺ (A ∧⁺ B) F = 
  expand⁺ A λ VA θ →
    expand⁺ B λ VB θ' → 
      F (∧⁺R (wk θ' VA) VB) (LIST.SET.trans-sub θ θ') 
expand⁺ ⊤⁺ F = F ⊤⁺R (λ x → x) 
expand⁺ (A ∨ B) F = 
  (expand⁺ A (λ V → F (∨R₁ V))) , (expand⁺ B (λ V → F (∨R₂ V)))
expand⁺ ⊥ F = <>
expand⁺ (↓ A) F = F (↓R (expand⁻ A (λ Sp θ → lfoc (θ Z) Sp))) LIST.SET.sub-wken 

expand⁻ (a Q .⁻) F = F id⁻ (λ x → x) 
expand⁻ (A ∧⁻ B) F = 
  (expand⁻ A (λ Sp → F (∧⁻L₁ Sp))) , (expand⁻ B (λ Sp → F (∧⁻L₂ Sp)))
expand⁻ ⊤⁻ F = <>
expand⁻ (A ⊃ B) F = 
  expand⁺ A λ V θ → 
    expand⁻ B λ Sp θ' → 
      F (⊃L (wk θ' V) Sp) (LIST.SET.trans-sub θ θ')
expand⁻ (↑ A) F = F (↑L (expand⁺ A (λ V θ → rfoc V))) (λ x → x)