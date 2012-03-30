
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
  ⟦⟧ : ZCtx
  _⟦_·⟦⟧⟧ : (Θ : ZCtx) (Δ : SCtx) → ZCtx
  _⟦⟦⟧·_⟧ : (Θ : ZCtx) (Δ : SCtx) → ZCtx

_⟦_⟧ : ZCtx → SCtx → SCtx 
⟦⟧ ⟦ Δ' ⟧ = Δ'
(Θ ⟦ Δ ·⟦⟧⟧) ⟦ Δ' ⟧ = Θ ⟦ Δ · Δ' ⟧
(Θ ⟦⟦⟧· Δ ⟧) ⟦ Δ' ⟧ = Θ ⟦ Δ' · Δ ⟧

_○_ : ZCtx → ZCtx → ZCtx
Θ ○ ⟦⟧ = Θ
Θ ○ (Θ' ⟦ Δ ·⟦⟧⟧) = (Θ ○ Θ') ⟦ Δ ·⟦⟧⟧
Θ ○ (Θ' ⟦⟦⟧· Δ ⟧) = (Θ ○ Θ') ⟦⟦⟧· Δ ⟧

data HCtx : Set where
  ⟪⟫ : HCtx
  _·⟪_⟪⟫⟫ : (Δ : SCtx) (Θ : HCtx) → HCtx
  ⟪_⟪⟫⟫·_ : (Θ : HCtx) (Δ : SCtx) → HCtx

_⟪_⟫ : HCtx → SCtx → SCtx
⟪⟫ ⟪ Δ' ⟫ = Δ'
(Δ ·⟪ Θ ⟪⟫⟫) ⟪ Δ' ⟫ = Δ · Θ ⟪ Δ' ⟫
(⟪ Θ ⟪⟫⟫· Δ) ⟪ Δ' ⟫ = Θ ⟪ Δ' ⟫ · Δ

elim⁺ : Type ⁺ → (SCtx → Set) → Set
elim⁺ (a Q .⁺) P = P ⟨⟨ a Q ⁺ ⟩⟩
elim⁺ (A ● B) P = elim⁺ A λ ΔA → elim⁺ B (λ ΔB → P (ΔA · ΔB))
elim⁺ ⊤⁺ P = P ∅
elim⁺ (A ⊕ B) P = elim⁺ A P × elim⁺ B P
elim⁺ ⊥ P = Unit
elim⁺ (↓ A) P = P ⟨ A ⟩

elim⁻ : Type ⁻ → (ZCtx → Conc → Set) → Set
elim⁻ (a Q .⁻) P = P ⟦⟧ ⟨⟨ a Q ⁻ ⟩⟩
elim⁻ (A & B) P = elim⁻ A P × elim⁻ B P
elim⁻ ⊤⁻ Θ = Unit
elim⁻ (A ->> B) P = elim⁺ A (λ ΔA → elim⁻ B (λ Θ U → P (Θ ⟦⟦⟧· ΔA ⟧) U))
elim⁻ (A >-> B) P = elim⁺ A (λ ΔA → elim⁻ B (λ Θ U → P (Θ ⟦ ΔA ·⟦⟧⟧) U))
elim⁻ (↑ A) P = P ⟦⟧ ⟨ A ⟩ 

data Prove (Δ : SCtx) : Conc → Set
data Spine : ZCtx → Type ⁻ → Conc → Set
data Value : (Δ : SCtx) → Type ⁺ → Set

data Value where
  hyp : ∀{A}
    → Value ⟨⟨ A ⟩⟩ A
  ↓R : ∀{A Δ}
    (N : elim⁻ A (λ Θ C → Prove (Θ ⟦ Δ ⟧) C))
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
    (Sp : Spine Θ A C)
    → Prove Δ C

data Spine where
  nil : ∀{A} → Spine ⟦⟧ A ⟨⟨ A ⟩⟩
  ↑L : ∀{A U} (Θ : ZCtx) 
    (N : elim⁺ A (λ Δ → Prove (Θ ⟦ Δ ⟧) U))
    → Spine Θ (↑ A) U
  &L₁ : ∀{Θ A B U} (Sp : Spine Θ A U) → Spine Θ (A & B) U
  &L₂ : ∀{Θ A B U} (Sp : Spine Θ B U) → Spine Θ (A & B) U
  ->>L : ∀{Θ Δ A B U}
    (V : Value Δ A)
    (Sp : Spine Θ B U) 
    → Spine (Θ ⟦⟦⟧· Δ ⟧) (A ->> B) U
  >->L : ∀{Θ Δ A B U}
    (V : Value Δ A)
    (Sp : Spine Θ B U) 
    → Spine (Θ ⟦ Δ ·⟦⟧⟧) (A >-> B) U

RInv : SCtx → Type ⁻ → Set
RInv Δ A = elim⁻ A (λ Θ U → Prove (Θ ⟦ Δ ⟧) U)

LInv : ZCtx → Type ⁺ → Conc → Set
LInv Θ A U = elim⁺ A (λ Δ → Prove (Θ ⟦ Δ ⟧) U)

map⁺ : (A : Type ⁺) {P : SCtx → Set}
  → ((Δ : SCtx) (V : Value Δ A) → P Δ) 
  → elim⁺ A P

map⁻ : (A : Type ⁻) {P : ZCtx → Conc → Set}
  → ((Θ : ZCtx) (U : Conc) (Sp : Spine Θ A U) → P Θ U)
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
map⁺ (↓ A) F = F ⟨ A ⟩ (↓R (map⁻ A (λ Θ U Sp → lfoc Θ refl Sp)))

map⁻ (a Q .⁻) F = F ⟦⟧ ⟨⟨ a Q ⁻ ⟩⟩ nil
map⁻ (A & B) F =
  (map⁻ A (λ Θ U Sp → F Θ U (&L₁ Sp))) , (map⁻ B (λ Θ U Sp → F Θ U (&L₂ Sp)))
map⁻ ⊤⁻ F = <>
map⁻ (A ->> B) F = 
  map⁺ A (λ Δ V → map⁻ B (λ Θ U Sp → F (Θ ⟦⟦⟧· Δ ⟧) U (->>L V Sp)))
map⁻ (A >-> B) F = 
  map⁺ A (λ Δ V → map⁻ B (λ Θ U Sp → F (Θ ⟦ Δ ·⟦⟧⟧) U (>->L V Sp)))
map⁻ (↑ A) F = F ⟦⟧ ⟨ A ⟩ (↑L ⟦⟧ (map⁺ A (λ Δ V → rfoc V)))



cut⁺ : ∀{Δ U} (A : Type ⁺) (Θ : ZCtx)
  → Value Δ A 
  → LInv Θ A U
  → Prove (Θ ⟦ Δ ⟧) U

cut⁻ : ∀{Δ U} (A : Type ⁻) (Θ : ZCtx)
  → RInv Δ A
  → Spine Θ A U
  → Prove (Θ ⟦ Δ ⟧) U

rsubstV : ∀{A Δ C} (Θ : HCtx)
  → RInv Δ A
  → Value (Θ ⟪ ⟨ A ⟩ ⟫) C
  → Value (Θ ⟪ Δ ⟫) C

rsubstN : ∀{A Δ U} (Θ : HCtx)
  → RInv Δ A
  → Prove (Θ ⟪ ⟨ A ⟩ ⟫) U
  → Prove (Θ ⟪ Δ ⟫) U

lsubstN : ∀{Δ A U} (Θ : ZCtx)
  → Prove Δ ⟨ A ⟩
  → LInv Θ A U
  → Prove (Θ ⟦ Δ ⟧) U

lsubstSp : ∀{B A U} (Θ Θ' : ZCtx)
  → Spine Θ' B ⟨ A ⟩
  → LInv Θ A U
  → Spine (Θ ○ Θ') B U

cut⁺ A Θ hyp N = {!!}
cut⁺ (A ● B) Θ (●R V₁ V₂) N = {!!}
--  cut⁺ A (Θ ⟪⟪⟫· _ ⟫) V₁ {!cut⁺ B (Θ ⟦ _ ·⟦⟧⟧) V₂ N!} --
cut⁺ ⊤⁺ Θ ⊤⁺R N = N
cut⁺ (A ⊕ B) Θ (⊕R₁ V) (N₁ , N₂) = cut⁺ A Θ V N₁
cut⁺ (A ⊕ B) Θ (⊕R₂ V) (N₁ , N₂) = cut⁺ B Θ V N₂
cut⁺ (↓ A) Θ (↓R N') N = {!!} -- rsubstN Θ N' N

cut⁻ A ⟦⟧ N nil = {!!}
cut⁻ (a Q .⁻) (Θ ⟦ Δ' ·⟦⟧⟧) N ()
cut⁻ (a Q .⁻) (Θ ⟦⟦⟧· Δ' ⟧) N ()
cut⁻ (A & B) Θ (N₁ , N₂) (&L₁ Sp) = cut⁻ A Θ N₁ Sp
cut⁻ (A & B) Θ (N₁ , N₂) (&L₂ Sp) = cut⁻ B Θ N₂ Sp
cut⁻ ⊤⁻ (Θ ⟦ Δ' ·⟦⟧⟧) N ()
cut⁻ ⊤⁻ (Θ ⟦⟦⟧· Δ' ⟧) N ()
cut⁻ (A ->> B) (Θ ⟦ Δ' ·⟦⟧⟧) N ()
cut⁻ (A ->> B) (Θ ⟦⟦⟧· Δ' ⟧) N (->>L V Sp) = {!!}
cut⁻ (A >-> B) (Θ ⟦ Δ' ·⟦⟧⟧) N (>->L V Sp) = {!!}
cut⁻ (A >-> B) (Θ ⟦⟦⟧· Δ' ⟧) N ()
cut⁻ (↑ A) Θ N (↑L .Θ N') = lsubstN Θ N N'

rsubstV (Δ' ·⟪ Θ ⟪⟫⟫) M (●R V₁ V₂) = ●R V₁ (rsubstV Θ M V₂)
rsubstV (⟪ Θ ⟪⟫⟫· Δ') M (●R V₁ V₂) = ●R (rsubstV Θ M V₁) V₂
rsubstV Θ M (↓R {C} N) = ↓R {!!}
rsubstV Θ M (⊕R₁ V) = ⊕R₁ (rsubstV Θ M V)
rsubstV Θ M (⊕R₂ V) = ⊕R₂ (rsubstV Θ M V)

rsubstN Θ M (rfoc V) = rfoc (rsubstV Θ M V)
rsubstN Θ M (lfoc Θ' eq Sp) = {!!}

lsubstN Θ (rfoc V) M = cut⁺ _ Θ V M
lsubstN Θ (lfoc Θ' Refl Sp) M = lfoc (Θ ○ Θ') {!!} (lsubstSp Θ Θ' Sp M)

lsubstSp Θ Θ' (↑L ._ N) M = {!!}
lsubstSp Θ Θ' (&L₁ Sp) M = &L₁ (lsubstSp Θ Θ' Sp M)
lsubstSp Θ Θ' (&L₂ Sp) M = &L₂ (lsubstSp Θ Θ' Sp M)
lsubstSp Θ (Θ' ⟦⟦⟧· Δ' ⟧) (->>L V Sp) M = ->>L V (lsubstSp Θ Θ' Sp M)
lsubstSp Θ (Θ' ⟦ Δ' ·⟦⟧⟧) (>->L V Sp) M = >->L V (lsubstSp Θ Θ' Sp M)


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

