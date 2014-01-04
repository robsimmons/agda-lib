
open import Prelude hiding (⊥; ⊤)
open import Foc hiding (Ctx)
open import Admissible hiding (_⊢_)
import Identity
import Cut

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

data SInv (Γ : Ctx) : Ctx × Propo → Set where
  Z : ∀{C}
    (D : Γ ⊢ C)
    → SInv Γ ([] , C)
  S : ∀{A Ψ C}
    (D : SInv (A :: Γ) (Ψ , C))
    → SInv Γ ((A :: Ψ) , C)

dZ : ∀{Γ A} → SInv Γ ([] , A) → Γ ⊢ A
dZ (Z D) = D

dS : ∀{Γ Ψ A B} → SInv Γ ((B :: Ψ) , A) → SInv (B :: Γ) (Ψ , A)
dS (S D) = D


-- Weakening

wk' : ∀{Γ Γ' A} → Γ ⊆ Γ' → Γ ⊢ A → Γ' ⊢ A
wk' θ (init x) = init (θ x)
wk' θ (⊥L x) = ⊥L (θ x)
wk' θ (∨R₁ D) = ∨R₁ (wk' θ D)
wk' θ (∨R₂ D) = ∨R₂ (wk' θ D)
wk' θ (∨L x D₁ D₂) = 
  ∨L (θ x) (wk' (LIST.SET.sub-cons-congr θ) D₁)
    (wk' (LIST.SET.sub-cons-congr θ) D₂)
wk' θ ⊤R = ⊤R
wk' θ (∧R D₁ D₂) = ∧R (wk' θ D₁) (wk' θ D₂)
wk' θ (∧L₁ x D) = ∧L₁ (θ x) (wk' (LIST.SET.sub-cons-congr θ) D)
wk' θ (∧L₂ x D) = ∧L₂ (θ x) (wk' (LIST.SET.sub-cons-congr θ) D)
wk' θ (⊃R D) = ⊃R (wk' (LIST.SET.sub-cons-congr θ) D)
wk' θ (⊃L x D₁ D₂) = ⊃L (θ x) (wk' θ D₁) (wk' (LIST.SET.sub-cons-congr θ) D₂)

wk'' : ∀{Γ Γ' C} → Γ ⊆ Γ' → SInv Γ C → SInv Γ' C
wk'' θ (Z D) = Z (wk' θ D)
wk'' θ (S D) = S (wk'' (LIST.SET.sub-cons-congr θ) D)

wken' : ∀{Γ A C} → Γ ⊢ C → (A :: Γ) ⊢ C
wken' = wk' LIST.SET.sub-wken

wkex' : ∀{Γ A B C} → (A :: Γ) ⊢ C → (A :: B :: Γ) ⊢ C
wkex' = wk' LIST.SET.sub-wkex

wkex2' : ∀{Γ A B C D} → (A :: B :: Γ) ⊢ D → (A :: B :: C :: Γ) ⊢ D
wkex2' = wk' (LIST.SET.sub-cons-congr LIST.SET.sub-wkex)

cntr' : ∀{Γ A C} → A ∈ Γ → (A :: Γ) ⊢ C → Γ ⊢ C
cntr' x = wk' (LIST.SET.sub-cntr x)

wken'' : ∀{Γ A C} → SInv Γ C → SInv (A :: Γ) C
wken'' = wk'' LIST.SET.sub-wken

wkex'' : ∀{Γ A B C} → SInv (A :: Γ) C → SInv (A :: B :: Γ) C
wkex'' = wk'' LIST.SET.sub-wkex

exch'' : ∀{Γ A B C} → SInv (B :: A :: Γ) C → SInv (A :: B :: Γ) C
exch'' = wk'' LIST.SET.sub-exch

exch2'' : ∀{Γ A B C D} → SInv (C :: A :: B :: Γ) D → SInv (A :: B :: C :: Γ) D
exch2'' = wk'' {!!}

{-


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

-}

-- Erasure

-- There is a small deviation from the Twelf proof and the article here,
-- because we define erasure over all sequents, not just suspension-normal
-- ones.

erase : ∀{⁼} → Type ⁼ → Propo
erase (a Q ⁼) = a Q ⁼
erase (↓ A) = erase A
erase ⊥ = ⊥
erase (A ∨ B) = erase A ∨ erase B
erase ⊤⁺ = ⊤
erase (A ∧⁺ B) = erase A ∧ erase B
erase (↑ A) = erase A
erase (A ⊃ B) = erase A ⊃ erase B
erase ⊤⁻ = ⊤
erase (A ∧⁻ B) = erase A ∧ erase B

erasehyp : (H : Hyp) → Propo
erasehyp (Susp A) = erase A
erasehyp (Pers A) = erase A

eraseΓ : List Hyp → Ctx
eraseΓ = LIST.map erasehyp

eraseU : (U : Conc) → Propo
eraseU (Inv A) = erase A
eraseU (True A) = erase A
eraseU (Susp A) = erase A

eraseseq : (F : SeqForm) → (Ctx × Propo)
eraseseq (Rfoc A) = [] , erase A
eraseseq (Left (Inl Ω) U) = LIST.map erase Ω , eraseU U
eraseseq (Left (Inr A) U) = [ erase A ] , eraseU U

-- Shift removal (not terribly elegant, but works for now)

not-doubleshifted : ∀{⁼} → Type ⁼ → Set
not-doubleshifted (a Q ⁼) = Unit
not-doubleshifted (↓ (a Q .⁻)) = Unit
not-doubleshifted (↓ (↑ A)) = Void
not-doubleshifted (↓ (A ⊃ A₁)) = Unit
not-doubleshifted (↓ ⊤⁻) = Unit
not-doubleshifted (↓ (A ∧⁻ A₁)) = Unit
not-doubleshifted ⊥ = Unit
not-doubleshifted (A ∨ A₁) = Unit
not-doubleshifted ⊤⁺ = Unit
not-doubleshifted (A ∧⁺ A₁) = Unit
not-doubleshifted (↑ (a Q .⁺)) = Unit
not-doubleshifted (↑ (↓ A)) = Void
not-doubleshifted (↑ ⊥) = Unit
not-doubleshifted (↑ (A ∨ A₁)) = Unit
not-doubleshifted (↑ ⊤⁺) = Unit
not-doubleshifted (↑ (A ∧⁺ A₁)) = Unit
not-doubleshifted (A ⊃ A₁) = Unit
not-doubleshifted ⊤⁻ = Unit
not-doubleshifted (A ∧⁻ A₁) = Unit 

rshifty : (A : Type ⁺)
  → ∃ λ B → ((erase A ≡ erase B) ×
             (not-doubleshifted B) × 
             (∀{Γ} → Term Γ [] (True B) → Term Γ [] (True A)))
rshifty (↓ (↑ A)) with rshifty A
... | B , refl , nds , fn = B , refl , nds , u↓↑R o fn
rshifty (a Q .⁺) = a Q ⁺ , Refl , <> , (λ x → x)
rshifty (↓ (a Q .⁻)) = ↓ (a Q ⁻) , Refl , <> , (λ x → x)
rshifty (↓ (A ⊃ B)) = ↓ (A ⊃ B) , Refl , <> , (λ x → x)
rshifty (↓ ⊤⁻) = ↓ ⊤⁻ , Refl , <> , (λ x → x)
rshifty (↓ (A ∧⁻ B)) = ↓ (A ∧⁻ B) , Refl , <> , (λ x → x)
rshifty ⊥ = ⊥ , Refl , <> , (λ x → x)
rshifty (A ∨ B) = (A ∨ B) , Refl , <> , (λ x → x)
rshifty ⊤⁺ = ⊤⁺ , Refl , <> , (λ x → x)
rshifty (A ∧⁺ B) = (A ∧⁺ B) , Refl , <> , (λ x → x)

lshifty : (A : Type ⁻)
  → ∃ λ B → ((erase A ≡ erase B) ×
             (not-doubleshifted B) ×
             (∀{Γ U} → stable U 
                → Term (Pers B :: Γ) [] U
                → Term (Pers A :: Γ) [] U))
lshifty (↑ (↓ A)) with lshifty A
... | B , refl , nds , fn = B , refl , nds , (λ pf D → u↑↓L pf (fn pf D))
lshifty (a Q .⁻) = (a Q ⁻) , Refl , <> , (λ _ x → x)
lshifty (↑ (a Q .⁺)) = ↑ (a Q ⁺) , Refl , <> , (λ _ x → x)
lshifty (↑ ⊥) = ↑ ⊥ , Refl , <> , (λ _ x → x)
lshifty (↑ (A ∨ B)) = ↑ (A ∨ B) , Refl , <> , (λ _ x → x)
lshifty (↑ ⊤⁺) = ↑ ⊤⁺ , Refl , <> , (λ _ x → x)
lshifty (↑ (A ∧⁺ B)) = ↑ (A ∧⁺ B) , Refl , <> , (λ _ x → x)
lshifty (A ⊃ B) = (A ⊃ B) , Refl , <> , (λ _ x → x)
lshifty ⊤⁻ = ⊤⁻ , Refl , <> , (λ _ x → x)
lshifty (A ∧⁻ B) = (A ∧⁻ B) , Refl , <> , (λ _ x → x)

{-
-- Erasure

eraseΓ : List (Type ⁺) → Ctx
eraseΓ [] = []
eraseΓ (A :: Γ) = eraseA A :: eraseΓ Γ

erasex : ∀{A Γ} → A ∈ Γ → eraseA A ∈ eraseΓ Γ
erasex Z = Z
erasex (S x) = S (erasex x)

stableΓ : List (Type ⁺) → Set
stableΓ = LIST.All stable

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
-}

-- De-focalization

sound : ∀{F Γ} → suspnormalΓ Γ → suspnormalF F
  → Exp Γ F
  → SInv (eraseΓ Γ) (eraseseq F)
sound pfΓ pf (id⁺ z) with pfΓ z
... | (Q , Refl) = Z (init (LIST.in-map erasehyp z))
sound pfΓ pf (↓R N) = sound pfΓ pf N
sound pfΓ pf (∨R₁ V) = Z (∨R₁ (dZ (sound pfΓ pf V)))
sound pfΓ pf (∨R₂ V) = Z (∨R₂ (dZ (sound pfΓ pf V)))
sound pfΓ pf ⊤⁺R = Z ⊤R
sound pfΓ pf (∧⁺R V₁ V₂) =
  Z (∧R (dZ (sound pfΓ pf V₁)) (dZ (sound pfΓ pf V₂)))
sound pfΓ pf (focR V) = sound pfΓ pf V
sound pfΓ pf (focL pf₁ x Sp) = 
  Z (cntr' (LIST.in-map erasehyp x) (dZ (dS (sound pfΓ pf Sp))))
sound pfΓ pf (η⁺ N) = S (sound (conssusp pfΓ) pf N)
sound pfΓ pf (↓L N) = S (sound (conspers pfΓ) pf N)
sound pfΓ pf ⊥L = S ⊥L'
 where
  ⊥L' : ∀{Ω Γ C}
    → SInv (⊥ :: Γ) (Ω , C)
  ⊥L' {[]} = Z (⊥L Z)
  ⊥L' {_ :: Ω} = S (exch'' ⊥L')
sound pfΓ pf (∨L N₁ N₂) = S (∨L' (dS (sound pfΓ pf N₁)) (dS (sound pfΓ pf N₂)))
 where 
  ∨L' : ∀{Ω Γ A B C}
    → SInv (A :: Γ) (Ω , C)
    → SInv (B :: Γ) (Ω , C)
    → SInv ((A ∨ B) :: Γ) (Ω , C)
  ∨L' {[]} (Z D₁) (Z D₂) = Z (∨L Z (wkex' D₁) (wkex' D₂))
  ∨L' {_ :: _} (S D₁) (S D₂) = S (exch'' (∨L' (exch'' D₁) (exch'' D₂)))
sound pfΓ pf (⊤⁺L N) = S (wken'' (sound pfΓ pf N))
sound pfΓ pf (∧⁺L N) = S (∧⁺L' (dS (dS (sound pfΓ pf N))))
 where
  ∧⁺L' : ∀{Ω Γ A B C}
    → SInv (B :: A :: Γ) (Ω , C)
    → SInv ((A ∧ B) :: Γ) (Ω , C)
  ∧⁺L' {[]} (Z D) = Z (∧L₁ Z (∧L₂ (S Z) (wkex2' D)))
  ∧⁺L' {x :: Ω} (S D) = S (exch'' (∧⁺L' (exch2'' D)))
sound pfΓ pf (η⁻ N) = sound pfΓ pf N
sound pfΓ pf (↑R N) = sound pfΓ pf N
sound pfΓ pf (⊃R N) = Z (⊃R (dZ (dS (sound pfΓ pf N))))
sound pfΓ pf ⊤⁻R = Z ⊤R
sound pfΓ pf (∧⁻R N₁ N₂) = Z (∧R (dZ (sound pfΓ pf N₁)) (dZ (sound pfΓ pf N₂)))
sound {Left ._ (Susp (a Q .⁻))} pfΓ <> id⁻ = S (Z (init Z))
sound {Left ._ (Susp (↑ _))} pfΓ () id⁻
sound {Left ._ (Susp (_ ⊃ _))} pfΓ () id⁻
sound {Left ._ (Susp ⊤⁻)} pfΓ () id⁻
sound {Left ._ (Susp (_ ∧⁻ _))} pfΓ () id⁻
sound pfΓ pf (↑L N) = sound pfΓ pf N
sound pfΓ pf (⊃L V Sp) =  S (Z (⊃L Z (wken' (dZ (sound pfΓ <> V)))
                                  (wkex' (dZ (dS (sound pfΓ pf Sp))))))
sound pfΓ pf (∧⁻L₁ Sp) = S (Z (∧L₁ Z (wkex' (dZ (dS (sound pfΓ pf Sp))))))
sound pfΓ pf (∧⁻L₂ Sp) = S (Z (∧L₂ Z (wkex' (dZ (dS (sound pfΓ pf Sp))))))


{-
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

foc {a Q .⁻} {Γ} pf (init x) with unerasex pf x 
... | Inr (_ , x' , ())
... | Inl (_ , x' , refl) = wk' (LIST.SET.sub-cntr x') (lem refl)
 where
  lem : ∀{B} → (a Q ⁻ ≡ eraseA B) 
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

foc {↑ (a Q .⁺)} {Γ} pf (init x) with unerasex pf x
... | Inr (._ , x' , Refl) = uinit⁺₂ x'
... | Inl (_ , x' , refl) = wk' (LIST.SET.sub-cntr x') (lem refl)
 where
  lem : ∀{B} → (a Q ⁺ ≡ eraseA B)
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

foc {C} {Γ} pf (⊥L x) with unerasex pf x
... | Inr (_ , x' , ()) 
... | Inl (_ , x' , refl) = wk' (LIST.SET.sub-cntr x') (lem refl)
 where
  lem : ∀{B} → (⊥ ≡ eraseA B)
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
  lem : ∀{B A₁ A₂} → (A₁ ∨ A₂ ≡ eraseA B)
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

foc {↑ ⊤⁺} pf ⊤R = u⊤⁺R

foc {⊤⁻} pf ⊤R = u⊤⁻R

foc {↑ (A ∧⁺ B)} pf (∧R D₁ D₂) = u∧⁺R (foc pf D₁) (foc pf D₂)

foc {A ∧⁻ B} pf (∧R D₁ D₂) = ∧⁻R (foc pf D₁) (foc pf D₂)

foc {C} {Γ} pf (∧L₁ x D) with unerasex pf x
... | Inr (_ , x' , ())
... | Inl (_ , x' , refl) = wk' (LIST.SET.sub-cntr x') (lem refl D)
 where
  lem : ∀{B A₁ A₂} → (A₁ ∧ A₂ ≡ eraseA B)
    → (A₁ :: eraseΓ Γ) ⊢ eraseA C
    → Term [] (↓ B :: Γ) [] (Reg C)
  lem {a Q .⁻} () D
  lem {↑ (a Q .⁺)} () D
  lem {↑ (↓ A)} refl' D = u↑↓L (lem refl' D)
  lem {↑ ⊥} () D 
  lem {↑ (A ∨ B)} () D
  lem {↑ ⊤⁺} () D 
  lem {↑ (A ∧⁺ B)} Refl D = 
    u∧⁺L (wk' LIST.SET.sub-wken (foc (LIST.ALL.cons <> pf) D))
  lem {A ⊃ B} () D
  lem {⊤⁻} () D
  lem {A ∧⁻ B} Refl D = u∧⁻L₁ (foc (LIST.ALL.cons <> pf) D)

foc {C} {Γ} pf (∧L₂ x D) with unerasex pf x
... | Inr (_ , x' , ())
... | Inl (_ , x' , refl) = wk' (LIST.SET.sub-cntr x') (lem refl D)
 where
  lem : ∀{B A₁ A₂} → (A₁ ∧ A₂ ≡ eraseA B)
    → (A₂ :: eraseΓ Γ) ⊢ eraseA C
    → Term [] (↓ B :: Γ) [] (Reg C)
  lem {a Q .⁻} () D
  lem {↑ (a Q .⁺)} () D
  lem {↑ (↓ A)} refl' D = u↑↓L (lem refl' D)
  lem {↑ ⊥} () D 
  lem {↑ (A ∨ B)} () D
  lem {↑ ⊤⁺} () D 
  lem {↑ (A ∧⁺ B)} Refl D = 
    u∧⁺L (wk' LIST.SET.sub-wkex (foc (LIST.ALL.cons <> pf) D))
  lem {A ⊃ B} () D
  lem {⊤⁻} () D
  lem {A ∧⁻ B} Refl D = u∧⁻L₂ (foc (LIST.ALL.cons <> pf) D)

foc {A ⊃ B} pf (⊃R D) = u⊃R (foc (LIST.ALL.cons <> pf) D)

foc {C} {Γ} pf (⊃L x D₁ D₂) with unerasex pf x
... | Inr (_ , x' , ())
... | Inl (_ , x' , refl) = wk' (LIST.SET.sub-cntr x') (lem refl D₁ D₂)
 where
  lem : ∀{B A₁ A₂} → (A₁ ⊃ A₂ ≡ eraseA B)
    → eraseΓ Γ ⊢ A₁
    → (A₂ :: eraseΓ Γ) ⊢ eraseA C
    → Term [] (↓ B :: Γ) [] (Reg C)
  lem {a Q .⁻} () D₁ D₂
  lem {↑ (a Q .⁺)} () D₁ D₂
  lem {↑ (↓ A)} refl' D₁ D₂ = u↑↓L (lem refl' D₁ D₂)
  lem {↑ ⊥} () D₁ D₂ 
  lem {↑ (A ∨ B)} () D₁ D₂
  lem {↑ ⊤⁺} () D₁ D₂ 
  lem {↑ (A ∧⁺ B)} () D₁ D₂
  lem {A ⊃ B} Refl D₁ D₂ = u⊃L (foc pf D₁) (foc (LIST.ALL.cons <> pf) D₂)
  lem {⊤⁻} () D₁ D₂ 
  lem {A ∧⁻ B} () D₁ D₂


-- Partial inverse of erasure

placeA : Propo → Type ⁻
placeA (a Q ⁺) = ↑ (a Q ⁺)
placeA (a Q ⁻) = a Q ⁻
placeA ⊥ = ↑ ⊥
placeA (A ∨ B) = ↑ (↓ (placeA A) ∨ ↓ (placeA B))
placeA ⊤ = ⊤⁻
placeA (A ∧ B) = placeA A ∧⁻ placeA B
placeA (A ⊃ B) = ↓ (placeA A) ⊃ placeA B 

eqA : (A : Propo) → A ≡ eraseA (placeA A)
eqA (a Q ⁺) = refl
eqA (a Q ⁻) = refl
eqA ⊥ = refl
eqA (A ∨ B) = lem (eqA A) (eqA B)
 where
  lem : ∀{A A' B B'} → A ≡ A' → B ≡ B' → Id {_} {Propo} (A ∨ B) (A' ∨ B')
  lem Refl Refl = refl
eqA ⊤ = refl
eqA (A ∧ B) = lem (eqA A) (eqA B)
 where
  lem : ∀{A A' B B'} → A ≡ A' → B ≡ B' → Id {_} {Propo} (A ∧ B) (A' ∧ B')
  lem Refl Refl = refl
eqA (A ⊃ B) = lem (eqA A) (eqA B)
 where
  lem : ∀{A A' B B'} → A ≡ A' → B ≡ B' → Id {_} {Propo} (A ⊃ B) (A' ⊃ B')
  lem Refl Refl = refl

placeΓ : Ctx → List (Type ⁺)
placeΓ [] = []
placeΓ (A :: Γ) = ↓ (placeA A) :: placeΓ Γ

eqΓ : (Γ : Ctx) → Γ ≡ eraseΓ (placeΓ Γ)
eqΓ [] = refl
eqΓ (A :: Γ) = lem (eqA A) (eqΓ Γ)
 where
  lem : ∀{A A' Γ Γ'} → A ≡ A' → Γ ≡ Γ' → Id {_} {Ctx} (A :: Γ) (A' :: Γ')
  lem Refl Refl = refl

place-stable : (Γ : Ctx) → (placeΓ Γ) stableΓ
place-stable [] ()
place-stable (A :: Γ) Z = <>
place-stable (A :: Γ) (S x) = place-stable Γ x


-- Corollaries of focalization

convert : ∀{A A' Γ Γ'} → Γ ≡ Γ' → A ≡ A' → Γ ⊢ A → Γ' ⊢ A'
convert Refl Refl D = D

cut : ∀{A C Γ} → Γ ⊢ A → (A :: Γ) ⊢ C → Γ ⊢ C
cut {A} {C} {Γ} D E = convert (symm (eqΓ Γ)) (symm (eqA C)) F
 where
  N : Term [] (placeΓ Γ) [] (Reg (placeA C))
  N = Cut.rsubstN [] 
        (foc (place-stable Γ) (convert (eqΓ Γ) (eqA A) D))
        (foc (place-stable (A :: Γ)) (convert (eqΓ (A :: Γ)) (eqA C) E))
 
  F : eraseΓ (placeΓ Γ) ⊢ eraseA (placeA C)
  F = denil (defocN N)

identity : ∀{A Γ} → (A :: Γ) ⊢ A
identity {A} {Γ} = convert (symm (eqΓ (A :: Γ))) (symm (eqA A)) D
 where
  N : Term [] (placeΓ (A :: Γ)) [] (Reg (placeA A))
  N = Identity.expand⁻ (↓L <> Z hyp⁻)

  D : eraseΓ (placeΓ (A :: Γ)) ⊢ eraseA (placeA A)
  D = denil (defocN N)

-}
