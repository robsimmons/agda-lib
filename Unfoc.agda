
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
{- 
  In order to keep ourselves from having to deal with quadratically-many
  vacuous cases in the proof of focalizaiton, this presentation of the
  sequent calculus is factored into three kinds of rules: initial, left,
  and right rules.
-}

data _⊢_ (Γ : Ctx) (C : Propo) : Set
data LD (Γ : Ctx) : Propo → Propo → Set
data RD (Γ : Ctx) : Propo → Set

data _⊢_ Γ C where
  init : ∀{Q ⁼}
    (x : a Q ⁼ ∈ Γ)
    → C ≡ a Q ⁼
    → Γ ⊢ C
  L : ∀{A}
    (x : A ∈ Γ)
    → LD Γ A C
    → Γ ⊢ C
  R : RD Γ C
    → Γ ⊢ C

data LD Γ where
  ⊥L : ∀{C}
    → LD Γ ⊥ C
  ∨L : ∀{A B C}
    (D₁ : (A :: Γ) ⊢ C)
    (D₂ : (B :: Γ) ⊢ C)
    → LD Γ (A ∨ B) C
  ∧L₁ : ∀{A B C}
    (D : (A :: Γ) ⊢ C)
    → LD Γ (A ∧ B) C
  ∧L₂ : ∀{A B C}
    (D : (B :: Γ) ⊢ C)
    → LD Γ (A ∧ B) C
  ⊃L : ∀{A B C}
    (D₁ : Γ ⊢ A)
    (D₂ : (B :: Γ) ⊢ C)
    → LD Γ (A ⊃ B) C

data RD Γ where
  ∨R₁ : ∀{A B}
    (D : Γ ⊢ A)
    → RD Γ (A ∨ B)
  ∨R₂ : ∀{A B}
    (D : Γ ⊢ B)
    → RD Γ (A ∨ B)
  ⊤R : RD Γ ⊤
  ∧R : ∀{A B}
    (D₁ : Γ ⊢ A)
    (D₂ : Γ ⊢ B)    
    → RD Γ (A ∧ B)  
  ⊃R : ∀{A B}
    (D : (A :: Γ) ⊢ B)
    → RD Γ (A ⊃ B)

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
wk' θ (init x Refl) = init (θ x) Refl
wk' θ (L x ⊥L) = L (θ x) ⊥L
wk' θ (R (∨R₁ D)) = R (∨R₁ (wk' θ D))
wk' θ (R (∨R₂ D)) = R (∨R₂ (wk' θ D))
wk' θ (L x (∨L D₁ D₂)) = 
  L (θ x) (∨L (wk' (LIST.SET.sub-cons-congr θ) D₁)
             (wk' (LIST.SET.sub-cons-congr θ) D₂))
wk' θ (R ⊤R) = R ⊤R
wk' θ (R (∧R D₁ D₂)) = R (∧R (wk' θ D₁) (wk' θ D₂))
wk' θ (L x (∧L₁ D)) = L (θ x) (∧L₁ (wk' (LIST.SET.sub-cons-congr θ) D))
wk' θ (L x (∧L₂ D)) = L (θ x) (∧L₂ (wk' (LIST.SET.sub-cons-congr θ) D))
wk' θ (R (⊃R D)) = R (⊃R (wk' (LIST.SET.sub-cons-congr θ) D))
wk' θ (L x (⊃L D₁ D₂)) = 
  L (θ x) (⊃L (wk' θ D₁) (wk' (LIST.SET.sub-cons-congr θ) D₂))

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
exch2'' = wk'' LIST.SET.sub-exch2


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

pull : ∀{Γ P} 
  → P ∈ eraseΓ Γ 
  → ∃ λ H → (H ∈ Γ) × (P ≡ erasehyp H)
pull {[]} ()
pull {H :: Γ} Z = H , Z , Refl
pull {_ :: Γ} (S x) with pull x 
... | H , y , refl = H , S y , refl


-- De-focalization

sound : ∀{F Γ} → suspnormalΓ Γ → suspnormalF F
  → Exp Γ F
  → SInv (eraseΓ Γ) (eraseseq F)
sound pfΓ pf (id⁺ z) with pfΓ z
... | (Q , Refl) = Z (init (LIST.in-map erasehyp z) Refl)
sound pfΓ pf (↓R N) = sound pfΓ pf N
sound pfΓ pf (∨R₁ V) = Z (R (∨R₁ (dZ (sound pfΓ pf V))))
sound pfΓ pf (∨R₂ V) = Z (R (∨R₂ (dZ (sound pfΓ pf V))))
sound pfΓ pf ⊤⁺R = Z (R ⊤R)
sound pfΓ pf (∧⁺R V₁ V₂) =
  Z (R (∧R (dZ (sound pfΓ pf V₁)) (dZ (sound pfΓ pf V₂))))
sound pfΓ pf (focR V) = sound pfΓ pf V
sound pfΓ pf (focL pf₁ x Sp) = 
  Z (cntr' (LIST.in-map erasehyp x) (dZ (dS (sound pfΓ pf Sp))))
sound pfΓ pf (η⁺ N) = S (sound (conssusp pfΓ) pf N)
sound pfΓ pf (↓L N) = S (sound (conspers pfΓ) pf N)
sound pfΓ pf ⊥L = S ⊥L'
 where
  ⊥L' : ∀{Ω Γ C}
    → SInv (⊥ :: Γ) (Ω , C)
  ⊥L' {[]} = Z (L Z ⊥L)
  ⊥L' {_ :: Ω} = S (exch'' ⊥L')
sound pfΓ pf (∨L N₁ N₂) = S (∨L' (dS (sound pfΓ pf N₁)) (dS (sound pfΓ pf N₂)))
 where 
  ∨L' : ∀{Ω Γ A B C}
    → SInv (A :: Γ) (Ω , C)
    → SInv (B :: Γ) (Ω , C)
    → SInv ((A ∨ B) :: Γ) (Ω , C)
  ∨L' {[]} (Z D₁) (Z D₂) = Z (L Z (∨L(wkex' D₁) (wkex' D₂)))
  ∨L' {_ :: _} (S D₁) (S D₂) = S (exch'' (∨L' (exch'' D₁) (exch'' D₂)))
sound pfΓ pf (⊤⁺L N) = S (wken'' (sound pfΓ pf N))
sound pfΓ pf (∧⁺L N) = S (∧⁺L' (dS (dS (sound pfΓ pf N))))
 where
  ∧⁺L' : ∀{Ω Γ A B C}
    → SInv (B :: A :: Γ) (Ω , C)
    → SInv ((A ∧ B) :: Γ) (Ω , C)
  ∧⁺L' {[]} (Z D) = Z (L Z (∧L₁ (L (S Z) (∧L₂ (wkex2' D)))))
  ∧⁺L' {x :: Ω} (S D) = S (exch'' (∧⁺L' (exch2'' D)))
sound pfΓ pf (η⁻ N) = sound pfΓ pf N
sound pfΓ pf (↑R N) = sound pfΓ pf N
sound pfΓ pf (⊃R N) = Z (R (⊃R (dZ (dS (sound pfΓ pf N)))))
sound pfΓ pf ⊤⁻R = Z (R ⊤R)
sound pfΓ pf (∧⁻R N₁ N₂) = 
  Z (R (∧R (dZ (sound pfΓ pf N₁)) (dZ (sound pfΓ pf N₂))))
sound {Left ._ (Susp (a Q .⁻))} pfΓ <> id⁻ = S (Z (init Z Refl))
sound {Left ._ (Susp (↑ _))} pfΓ () id⁻
sound {Left ._ (Susp (_ ⊃ _))} pfΓ () id⁻
sound {Left ._ (Susp ⊤⁻)} pfΓ () id⁻
sound {Left ._ (Susp (_ ∧⁻ _))} pfΓ () id⁻
sound pfΓ pf (↑L _ N) = sound pfΓ pf N
sound pfΓ pf (⊃L V Sp) =  S (Z (L Z (⊃L (wken' (dZ (sound pfΓ <> V)))
                                       (wkex' (dZ (dS (sound pfΓ pf Sp)))))))
sound pfΓ pf (∧⁻L₁ Sp) = S (Z (L Z (∧L₁ (wkex' (dZ (dS (sound pfΓ pf Sp)))))))
sound pfΓ pf (∧⁻L₂ Sp) = S (Z (L Z (∧L₂ (wkex' (dZ (dS (sound pfΓ pf Sp)))))))


-- Focalization

complete : ∀{U Γ} → suspnormalΓ Γ → suspstable U
  → (eraseΓ Γ) ⊢ (eraseU U)
  → Term Γ [] U

-- Focalization of left rules
-- Instead of the "lshifty" lemma we use an inner induction

complete pfΓ pf (L x D) with pull x 
complete {U} {Γ} pfΓ pf (L x D) | Pers A , y , Refl = cntr y (shifty A D)
 where
  shifty : (B : Type ⁻)
    → LD (eraseΓ Γ) (erase B) (eraseU U) 
    → Term (Pers B :: Γ) [] U
  shifty (a Q .⁻) ()
  shifty (↑ (a Q .⁺)) ()
  shifty (↑ (↓ A)) D = u↑↓L (fst pf) (shifty _ D)
  shifty (↑ ⊥) ⊥L = u⊥L (fst pf)
  shifty (↑ (A₁ ∨ A₂)) (∨L D₁ D₂) = 
    u∨L pfΓ pf (complete (conspers pfΓ) pf D₁) (complete (conspers pfΓ) pf D₂)
  shifty (↑ ⊤⁺) ()
  shifty (↑ (A₁ ∧⁺ A₂)) (∧L₁ D₁) =
    u∧⁺L pfΓ pf (wken (complete (conspers pfΓ) pf D₁))
  shifty (↑ (A₁ ∧⁺ A₂)) (∧L₂ D₁) = 
    u∧⁺L pfΓ pf (wkex (complete (conspers pfΓ) pf D₁))
  shifty (A₁ ⊃ A₂) (⊃L D₁ D₂) = 
    u⊃L pfΓ pf (complete pfΓ (<> , <>) D₁) (complete (conspers pfΓ) pf D₂)
  shifty ⊤⁻ ()
  shifty (A₁ ∧⁻ A₂) (∧L₁ D₁) = u∧⁻L₁ pfΓ (snd pf) (complete (conspers pfΓ) pf D₁)
  shifty (A₁ ∧⁻ A₂) (∧L₂ D₁) = u∧⁻L₂ pfΓ (snd pf) (complete (conspers pfΓ) pf D₁)

complete pfΓ pf (L x ()) | Susp (a Q .⁺) , y , Refl
complete pfΓ pf (L x D) | Susp (↓ (a Q .⁻)) , y , Refl with pfΓ y
... | _ , () 
complete pfΓ pf (L x D) | Susp (↓ (↑ A)) , y , Refl with pfΓ y
... | _ , () 
complete pfΓ pf (L x D) | Susp (↓ (A ⊃ A₁)) , y , Refl with pfΓ y
... | _ , () 
complete pfΓ pf (L x D) | Susp (↓ ⊤⁻) , y , Refl with pfΓ y
... | _ , () 
complete pfΓ pf (L x D) | Susp (↓ (A ∧⁻ A₁)) , y , Refl with pfΓ y
... | _ , () 
complete pfΓ pf (L x D) | Susp ⊥ , y , Refl with pfΓ y
... | _ , () 
complete pfΓ pf (L x D) | Susp (A ∨ A₁) , y , Refl with pfΓ y
... | _ , () 
complete pfΓ pf (L x D) | Susp ⊤⁺ , y , Refl with pfΓ y
... | _ , () 
complete pfΓ pf (L x D) | Susp (A ∧⁺ A₁) , y , Refl with pfΓ y
... | _ , () 

-- Focalization of right rules
-- Instead of the "rshifty" lemma we use an inner induction

complete {True A} {Γ} pfΓ pf (R D) = shifty A D
 where
  shifty : (B : Type ⁺)
    → RD (eraseΓ Γ) (erase B) 
    → Term Γ [] (True B)
  shifty (a Q .⁺) ()
  shifty (↓ (a Q .⁻)) ()
  shifty (↓ (↑ A)) D = u↓↑R (shifty A D)
  shifty (↓ (A₁ ⊃ A₂)) (⊃R D₁) = u⊃R pfΓ (complete (conspers pfΓ) pf D₁)
  shifty (↓ ⊤⁻) ⊤R = u⊤⁻R
  shifty (↓ (A₁ ∧⁻ A₂)) (∧R D₁ D₂) = 
    u∧⁻R pfΓ (complete pfΓ pf D₁) (complete pfΓ pf D₂)
  shifty ⊥ ()
  shifty (A₁ ∨ A₂) (∨R₁ D₁) = u∨R₁ pfΓ (complete pfΓ pf D₁)
  shifty (A₁ ∨ A₂) (∨R₂ D₁) = u∨R₂ pfΓ (complete pfΓ pf D₁)
  shifty ⊤⁺ ⊤R = u⊤⁺R
  shifty (A₁ ∧⁺ A₂) (∧R D₁ D₂) = 
    u∧⁺R pfΓ (complete pfΓ pf D₁) (complete pfΓ pf D₂)

complete {Inv A} pfΓ (() , snd) (R D)
complete {Susp (a _ ._)} _ (_ , _) (R ())
complete {Susp (↑ _)} pfΓ (_ , ()) _
complete {Susp (_ ⊃ _)} pfΓ (_ , ()) _
complete {Susp ⊤⁻} pfΓ (_ , ()) _
complete {Susp (_ ∧⁻ _)} _ (_ , ()) _

-- Focalization of the initial rule
-- This just ends up being a mess of work, mostly just handling all the
-- unsatisfiable patterns

complete {True A} pfΓ pf (init x refl) with pull x 
complete {True A} {Γ} pfΓ pf (init x refl) | Pers B , y , refl' = 
  cntr y (shifty B A refl refl')
 where
  shifty : ∀{Q ⁼} (B : Type ⁻) (A : Type ⁺)
    → erase A ≡ a Q ⁼
    → a Q ⁼ ≡ erase B
    → Term (Pers B :: Γ) [] (True A)
  shifty (↑ (↓ B)) A refl refl' = u↑↓L <> (shifty B A refl refl')
  shifty B (↓ (↑ A)) refl refl' = u↓↑R (shifty B A refl refl')
  shifty (a Q₁ .⁻) (↓ (a .Q₁ .⁻)) Refl Refl = uinit⁻
  shifty (↑ (a Q₁ .⁺)) (a .Q₁ .⁺) Refl Refl = uinit⁺
  shifty (a Q₁ .⁻) (a Q₂ .⁺) () Refl
  shifty (↑ (a Q₁ .⁺)) (↓ (a Q₂ .⁻)) () Refl
  shifty (↑ ⊥) _ _ ()
  shifty (↑ (B₁ ∨ B₂)) _ _ ()
  shifty (↑ ⊤⁺) _ _ ()
  shifty (↑ (B₁ ∧⁺ B₂)) _ _ ()
  shifty (B₁ ⊃ B₂) _ _ ()
  shifty ⊤⁻ _ _ ()
  shifty (B₁ ∧⁻ B₂) _ _ ()
  shifty _ (↓ (A₁ ⊃ A₂)) () _
  shifty _ (↓ ⊤⁻) () _
  shifty _ (↓ (A₁ ∧⁻ A₂)) () _
  shifty _ ⊥ () _
  shifty _ (A₁ ∨ A₂) () _
  shifty _ ⊤⁺ () _
  shifty _ (A₁ ∧⁺ A₂) () _

complete {True A} pfΓ pf (init x refl) | Susp B , y , refl' with pfΓ y
complete {True A} {Γ} pfΓ pf (init x refl) | Susp (a Q .⁺) , y , Refl | nz =
  cntr y (shifty A refl)
 where
  shifty : (B : Type ⁺)
    → erase B ≡ a Q ⁺
    → Term (Susp (a Q ⁺) :: Γ) [] (True B)
  shifty (a .Q .⁺) Refl = uinitsusp⁺
  shifty (↓ (a Q₁ .⁻)) ()
  shifty (↓ (↑ B)) refl' = u↓↑R (shifty B refl')
  shifty (↓ (B ⊃ B₁)) ()
  shifty (↓ ⊤⁻) ()
  shifty (↓ (B ∧⁻ B₁)) ()
  shifty ⊥ ()
  shifty (B ∨ B₁) ()
  shifty ⊤⁺ ()
  shifty (B ∧⁺ B₁) ()

complete {True A} pfΓ pf (init x refl) | Susp (↓ B) , y , refl' | _ , ()
complete {True A} pfΓ pf (init x refl) | Susp ⊥ , y , refl' | _ , ()
complete {True A} pfΓ pf (init x refl) | Susp (B ∨ B₁) , y , refl' | _ , ()
complete {True A} pfΓ pf (init x refl) | Susp ⊤⁺ , y , refl' | _ , ()
complete {True A} pfΓ pf (init x refl) | Susp (B ∧⁺ B₁) , y , refl' | _ , ()

complete {Susp (a Q .⁻)} pfΓ pf (init x Refl) with pull x 
complete {Susp (a Q .⁻)} {Γ} pfΓ pf (init x Refl) | Pers A , y , refl' =
  cntr y (shifty A refl')
 where
  shifty : (B : Type ⁻)
    → a Q ⁻ ≡ erase B
    → Term (Pers B :: Γ) [] (Susp (a Q ⁻))
  shifty (a .Q .⁻) Refl = uinitsusp⁻
  shifty (↑ (↓ B)) D = u↑↓L <> (shifty B D)
  shifty (↑ (a Q₁ .⁺)) ()
  shifty (↑ ⊥) ()
  shifty (↑ (B ∨ B₁)) ()
  shifty (↑ ⊤⁺) ()
  shifty (↑ (B ∧⁺ B₁)) ()
  shifty (B ⊃ B₁) ()
  shifty ⊤⁻ ()
  shifty (B ∧⁻ B₁) ()

complete {Susp (a Q₁ .⁻)} pfΓ pf (init x Refl) | Susp A , y , refl' with pfΓ y
complete {Susp (a Q₁ .⁻)} pfΓ pf (init x Refl) | Susp (a Q .⁺) , y , () | nz 
complete {Susp (a Q .⁻)} pfΓ pf (init x Refl) | Susp (↓ A) , y , _ | _ , ()
complete {Susp (a Q .⁻)} pfΓ pf (init x Refl) | Susp ⊥ , y , _ | _ , ()
complete {Susp (a Q .⁻)} pfΓ pf (init x Refl) | Susp (A ∨ A₁) , y , _ | _ , ()
complete {Susp (a Q .⁻)} pfΓ pf (init x Refl) | Susp ⊤⁺ , y , _ | _ , ()
complete {Susp (a Q .⁻)} pfΓ pf (init x Refl) | Susp (A ∧⁺ A₁) , y , _ | _ , ()

complete {Inv _} _ (() , _) (init _ _) 


-- Partial inverse of erasure

anno : Propo → Type ⁻
anno (a Q ⁺) = ↑ (a Q ⁺)
anno (a Q ⁻) = a Q ⁻
anno ⊥ = ↑ ⊥
anno (A ∨ B) = ↑ (↓ (anno A) ∨ ↓ (anno B))
anno ⊤ = ⊤⁻
anno (A ∧ B) = anno A ∧⁻ anno B
anno (A ⊃ B) = ↓ (anno A) ⊃ anno B 

eqA : (A : Propo) → A ≡ erase (anno A)
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

annoΓ : Ctx → List Hyp
annoΓ = LIST.map (Pers o anno)

eqΓ : (Γ : Ctx) → Γ ≡ eraseΓ (annoΓ Γ)
eqΓ [] = refl
eqΓ (A :: Γ) = LIST.cons-cong (eqA A) (eqΓ Γ)

annonormal : (Γ : Ctx) → suspnormalΓ (annoΓ Γ) 
annonormal [] () 
annonormal (A :: Γ) (S x) = annonormal Γ x

convert : ∀{A A' Γ Γ'} → Γ ≡ Γ' → A ≡ A' → Γ ⊢ A → Γ' ⊢ A'
convert Refl Refl D = D


-- Corollaries of focalization

cut : ∀{P Q Γ} → Γ ⊢ P → (P :: Γ) ⊢ Q → Γ ⊢ Q
cut {P} {Q} {Γ} D E = 
  convert (symm (eqΓ Γ)) (symm (eqA Q)) 
    (dZ (sound (annonormal Γ) <> N))
 where
  N : Term (annoΓ Γ) [] (True (↓ (anno Q)))
  N = Cut.lsubst (annonormal Γ) (<> , <>) 
        (complete (annonormal Γ) (<> , <>) (convert (eqΓ Γ) (eqA P) D))
        (↓L {A = anno P} (complete (conspers (annonormal Γ)) (<> , <>) 
               (convert (eqΓ (P :: Γ)) (eqA Q) E)))

identity : ∀{A Γ} → (A :: Γ) ⊢ A
identity {A} {Γ} = 
  convert (symm (eqΓ (A :: Γ))) (symm (eqA A)) 
    (dZ (sound (annonormal (A :: Γ)) <> N))
 where
  N : Term (Pers (anno A) :: annoΓ Γ) [] (Inv (anno A))
  N = Identity.expand⁻ (focL <> Z id⁻)

