
open import Prelude hiding (⊥)

module AltRigid where

data Polarity : Set where
  ⁺ : Polarity
  ⁻ : Polarity

-- Formulas 
infix 5 _●_
data Type : Polarity → Set where
   a : (Q : String) (⁼ : Polarity) → Type ⁼
   _●_ : (A B : Type ⁺) → Type ⁺
   ⊤⁺ : Type ⁺
   _⊕_ : (A B : Type ⁺) → Type ⁺
   ⊥ : Type ⁺
   _&_ : (A B : Type ⁻) → Type ⁻
   ⊤⁻ : Type ⁻
   _->>_ : (A : Type ⁺) (B : Type ⁻) → Type ⁻
   _>->_ : (A : Type ⁺) (B : Type ⁻) → Type ⁻
   ↓ : (A : Type ⁻) → Type ⁺
   ↑ : (A : Type ⁺) → Type ⁻

-- Contexts
infix 5 _·_
data SCtx : Set where
   ∅ : SCtx
   _·_ : (Δ₁ Δ₂ : SCtx) → SCtx
   ⟨_⟩ : (A : Type ⁻) → SCtx
   ⟨⟨_⟩⟩ : (A : Type ⁺) → SCtx

data Conc : Set where
   ⟨_⟩ : (A : Type ⁺) → Conc
   ⟨⟨_⟩⟩ : (A : Type ⁻) → Conc

-- Zipper contexts (standard zippers)
data ZCtx : Set where
   ⟨⟩ : ZCtx
   _⟦_·⟦⟧⟧ : (Θ : ZCtx) (Δ : SCtx) → ZCtx
   _⟦⟦⟧·_⟧ : (Θ : ZCtx) (Δ : SCtx) → ZCtx

_⟦_⟧ : ZCtx → SCtx → SCtx 
⟨⟩ ⟦ Δ' ⟧ = Δ'
(Θ ⟦ Δ ·⟦⟧⟧) ⟦ Δ' ⟧ = Θ ⟦ Δ · Δ' ⟧
(Θ ⟦⟦⟧· Δ ⟧) ⟦ Δ' ⟧ = Θ ⟦ Δ' · Δ ⟧

elim⁺ : Type ⁺ → (SCtx → Set) → Set
elim⁺ (a Q .⁺) P = P ⟨⟨ a Q ⁺ ⟩⟩
elim⁺ (A ● B) P = elim⁺ A λ ΔA → elim⁺ B (λ ΔB → P (ΔA · ΔB))
elim⁺ ⊤⁺ P = P ∅
elim⁺ (A ⊕ B) P = elim⁺ A P × elim⁺ B P
elim⁺ ⊥ P = Unit
elim⁺ (↓ A) P = P ⟨ A ⟩

elim⁻ : Type ⁻ → (ZCtx → Conc → Set) → Set
elim⁻ (a Q .⁻) P = P ⟨⟩ ⟨⟨ a Q ⁻ ⟩⟩
elim⁻ (A & B) P = elim⁻ A P × elim⁻ B P
elim⁻ ⊤⁻ Θ = Unit
elim⁻ (A ->> B) P = elim⁺ A (λ ΔA → elim⁻ B (λ Θ U → P (Θ ⟦⟦⟧· ΔA ⟧) U))
elim⁻ (A >-> B) P = elim⁺ A (λ ΔA → elim⁻ B (λ Θ U → P (Θ ⟦ ΔA ·⟦⟧⟧) U))
elim⁻ (↑ A) P = P ⟨⟩ ⟨ A ⟩ 

data Prove (Δ : SCtx) : Conc → Set
data Spine : ZCtx → Type ⁻ → Conc → Set
data Value : (Δ : SCtx) → Type ⁺ → Set

data Value where
  hyp : ∀{A}
    → Value ⟨⟨ A ⟩⟩ A
  ↓R : ∀{Δ A}
    → elim⁻ A (λ Θ C → Prove (Θ ⟦ Δ ⟧) C)
    → Value Δ (↓ A)
  ⊤⁺R : Value ∅ ⊤⁺
  ●R : ∀{Δ₁ Δ₂ A B}
    (V₁ : Value Δ₁ A)
    (V₂ : Value Δ₂ B)
    → Value (Δ₁ · Δ₂) (A ● B)
  ⊕R₁ : ∀{Δ A B}
    (V : Value Δ A)
    → Value Δ (A ⊕ B)
  ⊕R₂ : ∀{Δ A B}
    (V : Value Δ B)
    → Value Δ (A ⊕ B)

data Prove Δ where
  rfoc : ∀{A}
    (V : Value Δ A)
    → Prove Δ ⟨ A ⟩
  lfoc : ∀{A C} (Θ : ZCtx)
    (eq : Δ ≡ Θ ⟦ ⟨ A ⟩ ⟧)
    (S : Spine Θ A C)
    → Prove Δ C

data Spine where
  nil : ∀{A} → Spine ⟨⟩ A ⟨⟨ A ⟩⟩
  ↑L : ∀{A U} (Θ : ZCtx) 
    → elim⁺ A (λ Δ → Prove (Θ ⟦ Δ ⟧) U)
    → Spine ⟨⟩ (↑ A) U
  &L₁ : ∀{Θ A B U} (S : Spine Θ A U) → Spine Θ (A & B) U
  &L₂ : ∀{Θ A B U} (S : Spine Θ B U) → Spine Θ (A & B) U
  ->>L : ∀{Θ Δ A B U}
    (V : Value Δ A)
    (S : Spine Θ B U) 
    → Spine (Θ ⟦⟦⟧· Δ ⟧) (A ->> B) U
  >->L : ∀{Θ Δ A B U}
    (V : Value Δ A)
    (S : Spine Θ B U) 
    → Spine (Θ ⟦ Δ ·⟦⟧⟧) (A >-> B) U


map⁺ : (A : Type ⁺) {P : SCtx → Set}
  → ((Δ : SCtx) (V : Value Δ A) → P Δ) 
  → elim⁺ A P

map⁻ : (A : Type ⁻) {P : ZCtx → Conc → Set}
  → ((Θ : ZCtx) (U : Conc) (S : Spine Θ A U) → P Θ U)
  → elim⁻ A P

map⁺ (a Q .⁺) F = F ⟨⟨ a Q ⁺ ⟩⟩ hyp
map⁺ (A ● B) {P} F = 
  map⁺ A (λ ΔA VA → 
   map⁺ B (λ ΔB VB → 
     F (ΔA · ΔB) (●R VA VB)))
map⁺ ⊤⁺ F = F ∅ ⊤⁺R
map⁺ (A ⊕ B) F = 
  (map⁺ A (λ Δ V → F Δ (⊕R₁ V))) , (map⁺ B (λ Δ V → F Δ (⊕R₂ V)))
map⁺ ⊥ F = <>
map⁺ (↓ A) F = F ⟨ A ⟩ (↓R (map⁻ A (λ Θ U S' → lfoc Θ refl S')))

map⁻ (a Q .⁻) F = F ⟨⟩ ⟨⟨ a Q ⁻ ⟩⟩ nil
map⁻ (A & B) F =
  (map⁻ A (λ Θ U S' → F Θ U (&L₁ S'))) , (map⁻ B (λ Θ U S' → F Θ U (&L₂ S')))
map⁻ ⊤⁻ F = <>
map⁻ (A ->> B) F = 
  map⁺ A (λ Δ V → map⁻ B (λ Θ U S' → F (Θ ⟦⟦⟧· Δ ⟧) U (->>L V S')))
map⁻ (A >-> B) F = 
  map⁺ A (λ Δ V → map⁻ B (λ Θ U S' → F (Θ ⟦ Δ ·⟦⟧⟧) U (>->L V S')))
map⁻ (↑ A) F = F ⟨⟩ ⟨ A ⟩ (↑L ⟨⟩ (map⁺ A (λ Δ V → rfoc V)))


p1 = a "A" ⁺
p2 = a "B" ⁺
p3 = a "C" ⁺
p4 = a "D" ⁺
p5 = a "E" ⁺

qqq : Value ∅ (↓ (p1 >-> (p2 >-> (p3 ->> (p4 ->> (p5 >-> ↑ p5))))))
qqq = ↓R {!!}

subst⁺ : ∀{Δ A U} (Θ : ZCtx) → Value Δ A → Prove (Θ ⟦ ⟨⟨ A ⟩⟩ ⟧) U → Prove (Θ ⟦ Δ ⟧) U
subst⁺ V N = {!!}


id⁺ : ∀{C} (Θ : ZCtx) (A : Type ⁺) 
  → Prove (Θ ⟦ ⟨⟨ A ⟩⟩ ⟧) C
  → elim⁺ A (λ Δ → Prove (Θ ⟦ Δ ⟧) C)
id⁺ Θ A N = map⁺ A (λ Δ V → subst⁺ Θ V N)

