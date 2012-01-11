
open import Prelude hiding (⊥; ⊤)
open import Foc hiding (Ctx; wk') renaming (wk to wk')
open import Admissible hiding (_⊢_)

module Unfoc where

data Propo : Set where
  a : (Q : String) (⁼ : Polarity) → Propo
  ⊥ : Propo
  _∨_ : (A B : Propo) → Propo
  ⊤ : Propo
  _∧_ : (A B : Propo) → Propo
  _⊃_ : (A B : Propo) → Propo

Ctx = List Propo


-- Sequent Calculus

data _⊢_ (Γ : Ctx) : Propo → Set where
  init : ∀{Q ⁼}
    (x : (a Q ⁼) ∈ Γ)
    → Γ ⊢ (a Q ⁼)
  ⊥L : ∀{C}
    (x : ⊥ ∈ Γ)
    → Γ ⊢ C
  ∨R₁ : ∀{A B}
    (D : Γ ⊢ A)
    → Γ ⊢ (A ∨ B)
  ∨R₂ : ∀{A B}
    (D : Γ ⊢ B)
    → Γ ⊢ (A ∨ B)
  ∨L : ∀{A B C}
    (x : (A ∨ B) ∈ Γ)
    (D₁ : (A :: Γ) ⊢ C)
    (D₂ : (B :: Γ) ⊢ C)
    → Γ ⊢ C
  ⊤R : Γ ⊢ ⊤
  ∧R : ∀{A B}
    (D₁ : Γ ⊢ A)
    (D₂ : Γ ⊢ B)    
    → Γ ⊢ (A ∧ B)
  ∧L₁ : ∀{A B C}
    (x : (A ∧ B) ∈ Γ)
    (D : (A :: Γ) ⊢ C)
    → Γ ⊢ C
  ∧L₂ : ∀{A B C}
    (x : (A ∧ B) ∈ Γ)
    (D : (B :: Γ) ⊢ C)
    → Γ ⊢ C
  ⊃R : ∀{A B}
    (D : (A :: Γ) ⊢ B)
    → Γ ⊢ (A ⊃ B)
  ⊃L : ∀{A B C}
    (x : (A ⊃ B) ∈ Γ)
    (D₁ : Γ ⊢ A)
    (D₂ : (B :: Γ) ⊢ C)
    → Γ ⊢ C

data SInv (Γ : Ctx) : Ctx → Propo → Set where
  Nil : ∀{C}
    (D : Γ ⊢ C)
    → SInv Γ [] C
  Cons : ∀{A Ψ C}
    (D : SInv (A :: Γ) Ψ C)
    → SInv Γ (A :: Ψ) C

denil : ∀{Γ A} → SInv Γ [] A → Γ ⊢ A
denil (Nil D) = D

decons : ∀{Γ Ψ A B} → SInv Γ (B :: Ψ) A → SInv (B :: Γ) Ψ A
decons (Cons D) = D

-- Weakening

wk : ∀{Γ Γ' A} → Γ ⊆ Γ' → Γ ⊢ A → Γ' ⊢ A
wk θ (init x) = init (θ x)
wk θ (⊥L x) = ⊥L (θ x)
wk θ (∨R₁ D) = ∨R₁ (wk θ D)
wk θ (∨R₂ D) = ∨R₂ (wk θ D)
wk θ (∨L x D₁ D₂) = 
  ∨L (θ x) (wk (LIST.SET.sub-cons-congr θ) D₁)
    (wk (LIST.SET.sub-cons-congr θ) D₂)
wk θ ⊤R = ⊤R
wk θ (∧R D₁ D₂) = ∧R (wk θ D₁) (wk θ D₂)
wk θ (∧L₁ x D) = ∧L₁ (θ x) (wk (LIST.SET.sub-cons-congr θ) D)
wk θ (∧L₂ x D) = ∧L₂ (θ x) (wk (LIST.SET.sub-cons-congr θ) D)
wk θ (⊃R D) = ⊃R (wk (LIST.SET.sub-cons-congr θ) D)
wk θ (⊃L x D₁ D₂) = ⊃L (θ x) (wk θ D₁) (wk (LIST.SET.sub-cons-congr θ) D₂)

wk-prop1 : ∀{A B Γ} (Γ' : Ctx) → (Γ' ++ A :: Γ) ⊆ (A :: Γ' ++ B :: Γ) 
wk-prop1 [] Z = Z
wk-prop1 [] (S n) = S (S n)
wk-prop1 (A :: Γ') Z = S Z
wk-prop1 (A :: Γ') (S n) = LIST.SET.sub-wkex (wk-prop1 Γ' n)

wk-prop2 : ∀{B Γ} (Γ' : Ctx) → (Γ' ++ Γ) ⊆ (Γ' ++ B :: Γ) 
wk-prop2 [] x = S x
wk-prop2 (A :: Γ') Z = Z
wk-prop2 (A :: Γ') (S n) = S (wk-prop2 Γ' n)

wk-prop3 : ∀{A B C Γ} (Γ' : Ctx)
  → (Γ' ++ A :: B :: Γ) ⊆ (A :: B :: Γ' ++ C :: Γ)
wk-prop3 [] Z = Z
wk-prop3 [] (S Z) = S Z
wk-prop3 [] (S (S n)) = S (S (S n))
wk-prop3 (A' :: Γ') Z = S (S Z)
wk-prop3 (A' :: Γ') (S n) with wk-prop3 Γ' n
... | Z = Z
... | (S Z) = S Z
... | (S (S n')) = S (S (S n'))

-- Erasure

eraseA : ∀{⁼} → Type ⁼ → Propo
eraseA (a Q ⁼) = a Q ⁼
eraseA (↓ A) = eraseA A
eraseA ⊥ = ⊥
eraseA (A ∨ B) = eraseA A ∨ eraseA B
eraseA ⊤⁺ = ⊤
eraseA (A ∧⁺ B) = eraseA A ∧ eraseA B
eraseA (↑ A) = eraseA A
eraseA (A ⊃ B) = eraseA A ⊃ eraseA B
eraseA ⊤⁻ = ⊤
eraseA (A ∧⁻ B) = eraseA A ∧ eraseA B

eraseΓ : List (Type ⁺) → Ctx
eraseΓ [] = []
eraseΓ (A :: Γ) = eraseA A :: eraseΓ Γ

erasex : ∀{A Γ} → A ∈ Γ → eraseA A ∈ eraseΓ Γ
erasex Z = Z
erasex (S x) = S (erasex x)

_stableΓ : List (Type ⁺) → Set
_stableΓ = LIST.All _stable⁺ 

unerasex : ∀{Γ A} 
  → Γ stableΓ
  → A ∈ eraseΓ Γ 
  → (∃ λ B → (↓ B ∈ Γ) × (A ≡ eraseA B))
    + (∃ λ Q → (a Q ⁺ ∈ Γ) × (A ≡ a Q ⁺))
unerasex {[]} pf ()
unerasex {A :: xs} pf Z with pf Z 
unerasex {a Q .⁺ :: xs} pf Z | pf' = Inr (_ , Z , refl)
unerasex {↓ A :: xs} pf Z | pf' = Inl (_ , Z , refl)
unerasex {⊥ :: xs} pf Z | ()
unerasex {A ∨ B :: xs} pf Z | ()
unerasex {⊤⁺ :: xs} pf Z | ()
unerasex {A ∧⁺ B :: xs} pf Z | ()
unerasex {_ :: _} pf (S x) with unerasex (λ x' → pf (S x')) x
... | Inl (_ , x' , refl) = Inl (_ , S x' , refl)
... | Inr (_ , x' , refl) = Inr (_ , S x' , refl)

-- Defocalization

defocV : ∀{Γ A} → Value [] Γ A → eraseΓ Γ ⊢ eraseA A
defocN : ∀{Γ Ω A} → Term [] Γ Ω (Reg A) → SInv (eraseΓ Γ) (eraseΓ Ω) (eraseA A)
defocSp : ∀{Γ A B} → Spine [] Γ A (Reg B) → (eraseA A :: eraseΓ Γ) ⊢ eraseA B

defocV (hyp⁺ ())
defocV (pR x) = init (erasex x)
defocV (↓R N) = denil (defocN N)
defocV (∨R₁ V) = ∨R₁ (defocV V)
defocV (∨R₂ V) = ∨R₂ (defocV V)
defocV ⊤⁺R = ⊤R
defocV (∧⁺R V₁ V₂) = ∧R (defocV V₁) (defocV V₂)

defocN (L pf⁺ N) = Cons (defocN N)
defocN (↓L pf⁻ x Sp) = Nil (wk (LIST.SET.sub-cntr (erasex x)) (defocSp Sp))
defocN ⊥L = Cons (⊥L' _ [])
 where
  ⊥L' : ∀{Γ A} (Ω Γ' : Ctx) → SInv (Γ' ++ ⊥ :: Γ) Ω A 
  ⊥L' [] Γ' = Nil (⊥L (LIST.SET.sub-appendl _ Γ' Z))
  ⊥L' (A :: Ω) Γ' = Cons (⊥L' Ω (A :: Γ'))
defocN (∨L N₁ N₂) = Cons (∨L' _ [] (decons (defocN N₁)) (decons (defocN N₂)))
 where
  ∨L' : ∀{Γ A B C} (Ω Γ' : Ctx) 
    → SInv (Γ' ++ A :: Γ) Ω C 
    → SInv (Γ' ++ B :: Γ) Ω C 
    → SInv (Γ' ++ (A ∨ B) :: Γ) Ω C 
  ∨L' [] Γ' (Nil D) (Nil E) = 
    Nil (∨L (LIST.SET.sub-appendl _ Γ' Z) 
          (wk (wk-prop1 Γ') D) 
          (wk (wk-prop1 Γ') E))
  ∨L' (A :: Ω) Γ' (Cons D) (Cons E) = Cons (∨L' Ω (_ :: Γ') D E)
defocN (⊤⁺L N) = Cons (⊤⁺L' _ [] (defocN N))
 where
  ⊤⁺L' : ∀{Γ C} (Ω Γ' : Ctx)
    → SInv (Γ' ++ Γ) Ω C
    → SInv (Γ' ++ ⊤ :: Γ) Ω C
  ⊤⁺L' [] Γ' (Nil D) = Nil (wk (wk-prop2 Γ') D)
  ⊤⁺L' (A :: Ω) Γ' (Cons D) = Cons (⊤⁺L' Ω (_ :: Γ') D)
defocN (∧⁺L N) = Cons (∧⁺L' _ [] (decons (decons (defocN N))))
 where
  ∧⁺L' : ∀{Γ A B C} (Ω Γ' : Ctx)
    → SInv (Γ' ++ B :: A :: Γ) Ω C
    → SInv (Γ' ++ (A ∧ B) :: Γ) Ω C
  ∧⁺L' [] Γ' (Nil D) = 
    Nil (∧L₁ (LIST.SET.sub-appendl _ Γ' Z)
          (∧L₂ (S (LIST.SET.sub-appendl _ Γ' Z)) 
            (wk (wk-prop3 Γ') D)))
  ∧⁺L' (A :: Ω) Γ' (Cons D) = Cons (∧⁺L' Ω (_ :: Γ') D)
defocN (↑R V) = Nil (defocV V)
defocN (⊃R N) = Nil (⊃R (denil (decons (defocN N))))
defocN ⊤⁻R = Nil ⊤R
defocN (∧⁻R N₁ N₂) = Nil (∧R (denil (defocN N₁)) (denil (defocN N₂)))

defocSp pL = init Z
defocSp (↑L N) = denil (decons (defocN N))
defocSp (⊃L V Sp) = 
  ⊃L Z (wk LIST.SET.sub-wken (defocV V)) 
    (wk LIST.SET.sub-wkex (defocSp Sp))
defocSp (∧⁻L₁ Sp) = ∧L₁ Z (wk LIST.SET.sub-wkex (defocSp Sp))
defocSp (∧⁻L₂ Sp) = ∧L₂ Z (wk LIST.SET.sub-wkex (defocSp Sp))

-- Focalization

atom-lem : ∀{Q Q' P1 P2} → Id {_} {Propo} (a Q P1) (a Q' P2) → P1 ≡ P2
atom-lem Refl = Refl

foc : ∀{A Γ} → Γ stableΓ → (eraseΓ Γ) ⊢ (eraseA A) → Term [] Γ [] (Reg A) 

foc {a Q .⁻} pf (init x) with unerasex pf x 
... | Inr (_ , x' , ())
... | Inl (_ , x' , refl) = wk' (LIST.SET.sub-cntr x') (lem refl)
 where
  lem : ∀{B Γ} → (a Q ⁻ ≡ eraseA B) 
    → Term [] (↓ B :: Γ) [] (Reg (a Q ⁻))
  lem {a .Q .⁻} Refl = uinit⁻
  lem {↑ (a Q' .⁺)} refl' with atom-lem refl'
  ... | ()
  lem {↑ (↓ A)} refl' = u↑↓L (lem {A} refl')
  lem {↑ ⊥} ()
  lem {↑ (A ∨ B)} ()
  lem {↑ ⊤⁺} ()
  lem {↑ (A ∧⁺ B)} ()
  lem {A ⊃ B} ()
  lem {⊤⁻} ()
  lem {A ∧⁻ B} ()

foc {↑ (a Q .⁺)} pf (init x) with unerasex pf x
... | Inr (._ , x' , Refl) = uinit⁺₂ x'
... | Inl (_ , x' , refl) = wk' (LIST.SET.sub-cntr x') (lem refl)
 where
  lem : ∀{B Γ} → (a Q ⁺ ≡ eraseA B)
    → Term [] (↓ B :: Γ) [] (Reg (↑ (a Q ⁺)))
  lem {a Q' .⁻} refl' with atom-lem refl'
  ... | ()
  lem {↑ (a .Q .⁺)} Refl = uinit⁺₁
  lem {↑ (↓ A)} refl' = u↑↓L (lem {A} refl')
  lem {↑ ⊥} ()
  lem {↑ (A ∨ B)} ()
  lem {↑ ⊤⁺} ()
  lem {↑ (A ∧⁺ B)} ()
  lem {A ⊃ B} ()
  lem {⊤⁻} ()
  lem {A ∧⁻ B} ()

foc {↑ (↓ A)} pf D = u↑↓R (foc {A} pf D) 

foc {A} pf (⊥L x) with unerasex pf x
... | Inr (_ , x' , ()) 
... | Inl (_ , x' , refl) = wk' (LIST.SET.sub-cntr x') (lem refl)
 where
  lem : ∀{B Γ C} → (⊥ ≡ eraseA B)
    → Term [] (↓ B :: Γ) [] (Reg C)
  lem {a Q .⁻} ()
  lem {↑ (a Q .⁺)} ()
  lem {↑ (↓ A')} refl' = u↑↓L (lem {A'} refl')
  lem {↑ ⊥} refl' = u⊥L
  lem {↑ (A' ∨ B)} ()
  lem {↑ ⊤⁺} ()
  lem {↑ (A' ∧⁺ B)} ()
  lem {A' ⊃ B} ()
  lem {⊤⁻} ()
  lem {A' ∧⁻ B} ()

foc {↑ (A ∨ B)} pf (∨R₁ D) = u∨R₁ (foc pf D)

foc {↑ (A ∨ B)} pf (∨R₂ D) = u∨R₂ (foc pf D)

foc {C} {Γ} pf (∨L x D₁ D₂) with unerasex pf x
... | Inr (_ , x' , ())
... | Inl (_ , x' , refl) = wk' (LIST.SET.sub-cntr x') (lem refl D₁ D₂)
 where
  lem : ∀{B A₁ A₂ C} → (A₁ ∨ A₂ ≡ eraseA B)
    → (A₁ :: eraseΓ Γ) ⊢ eraseA C
    → (A₂ :: eraseΓ Γ) ⊢ eraseA C
    → Term [] (↓ B :: Γ) [] (Reg C)
  lem {a Q .⁻} () D₁ D₂
  lem {↑ (a Q .⁺)} () D₁ D₂
  lem {↑ (↓ A')} refl' D₁ D₂ = u↑↓L (lem refl' D₁ D₂)
  lem {↑ ⊥} () D₁ D₂
  lem {↑ (A' ∨ B)} Refl D₁ D₂ = 
    u∨L (foc (LIST.ALL.cons <> pf) D₁) (foc (LIST.ALL.cons <> pf) D₂)
  lem {↑ ⊤⁺} () D₁ D₂
  lem {↑ (A' ∧⁺ B)} () D₁ D₂
  lem {A' ⊃ B} () D₁ D₂
  lem {⊤⁻} () D₁ D₂
  lem {A' ∧⁻ B} () D₁ D₂

foc {↑ ⊤⁺} pf ⊤R = {!!}
foc {↑ (A ∧⁺ B)} pf (∧R D₁ D₂) = {!!}
foc {A ⊃ B} pf (⊃R D) = {!!}
foc {⊤⁻} pf ⊤R = {!!}
foc {A ∧⁻ B} pf (∧R D₁ D₂) = {!!}



foc {A} pf (∧L₁ x D) = {!!}
foc {A} pf (∧L₂ x D) = {!!}
foc {A} pf (⊃L x D₁ D₂) = {!!}
