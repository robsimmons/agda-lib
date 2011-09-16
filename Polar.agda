{-# OPTIONS --no-termination-check #-}

open import Prelude hiding (⊤)

module Polar where

data Pol : Set where
  ⁻ : Pol
  ⁺ : Pol  
 
data Type : Pol → Set where
  c : {⁼ : Pol} (Q : String) → Type ⁼
  ↓ : (A⁻ : Type ⁻) → Type ⁺
  ↑ : (Δ : List (Type ⁺)) → Type ⁻
  false : Type ⁺ 
  _⊕_ : (A⁺ B⁺ : Type ⁺) → Type ⁺ 
  true : Type ⁺
  _⊗_ : (A⁺ B⁺ : Type ⁺) → Type ⁺
  ⊤ : Type ⁻
  _&_ : (A⁻ B⁻ : Type ⁻) → Type ⁻
  _⊸_ : (Δ : List (Type ⁺)) (B⁻ : Type ⁻) → Type ⁻

data Atomic : Type ⁻ → Set where
  c : ∀{Q} → Atomic (c Q)
  ↑ : ∀{A⁺} → Atomic (↑ A⁺)

Ctx = List (Type ⁻ + String)

_⊆_ : Ctx → Ctx → Set
_⊆_ = LIST.SET.Sub

infix 1 _⊢_
infix 1 _[_]⊢_
infix 1 _⊢[_]
infix 1 _∣_⊢_

mutual
  data _⊢_ (Γ : Ctx) : Type ⁻ → Set where
    foc : ∀{A⁻ γ}
      (x : Inl A⁻ ∈ Γ)
      (atm : Atomic γ)
      (Sp : Γ [ A⁻ ]⊢ γ)
      → Γ ⊢ γ
    ↑R : ∀{Δ}
      (σ : Γ ⊢[ Δ ])
      → Γ ⊢ ↑ Δ 
    ⊤R : Γ ⊢ ⊤ 
    &R : ∀{A⁻ B⁻}
      (N₁ : Γ ⊢ A⁻)
      (N₂ : Γ ⊢ B⁻)
      → Γ ⊢ A⁻ & B⁻
    ⊸R : ∀{Δ B⁻}
      (N : Γ ∣ Δ ⊢ B⁻)
      → Γ ⊢ Δ ⊸ B⁻
  
  data _[_]⊢_ (Γ : Ctx) : Type ⁻ → Type ⁻ → Set where
    nil : ∀{Q}
      → Γ [ c Q ]⊢ c Q
    cont : ∀{Δ C⁻}
      (N : Γ ∣ Δ ⊢ C⁻)
      → Γ [ ↑ Δ ]⊢ C⁻
    &L₁ : ∀{A⁻ B⁻ C⁻}
      (Sp : Γ [ A⁻ ]⊢ C⁻)
      → Γ [ A⁻ & B⁻ ]⊢ C⁻
    &L₂ : ∀{A⁻ B⁻ C⁻}
      (Sp : Γ [ B⁻ ]⊢ C⁻)
      → Γ [ A⁻ & B⁻ ]⊢ C⁻
    ⊸L : ∀{Δ B⁻ C⁻}
      (σ : Γ ⊢[ Δ ])
      (Sp : Γ [ B⁻ ]⊢ C⁻)
      → Γ [ Δ ⊸ B⁻ ]⊢ C⁻ 

  data _⊢[_] (Γ : Ctx) : List (Type ⁺) → Set where
    nil : Γ ⊢[ [] ]
    cR : ∀{Q Δ}
      (x : Inr Q ∈ Γ)
      (σ : Γ ⊢[ Δ ])
      → Γ ⊢[ c Q :: Δ ]
    ↓R : ∀{A⁻ Δ}
      (N : Γ ⊢ A⁻)
      (σ : Γ ⊢[ Δ ])
      → Γ ⊢[ ↓ A⁻ :: Δ ]
    ⊕R₁ : ∀{A⁺ B⁺ Δ}
      (σ : Γ ⊢[ A⁺ :: Δ ])
      → Γ ⊢[ A⁺ ⊕ B⁺ :: Δ ]
    ⊕R₂ : ∀{A⁺ B⁺ Δ}
      (σ : Γ ⊢[ B⁺ :: Δ ])
      → Γ ⊢[ A⁺ ⊕ B⁺ :: Δ ]
    trueR : ∀{Δ}
      (σ : Γ ⊢[ Δ ])
      → Γ ⊢[ true :: Δ ]
    ⊗R : ∀{A⁺ B⁺ Δ}
      (σ : Γ ⊢[ A⁺ :: B⁺ :: Δ ])
      → Γ ⊢[ A⁺ ⊗ B⁺ :: Δ ]

  data _∣_⊢_ (Γ : Ctx) : List (Type ⁺) → Type ⁻ → Set where
    nil : ∀{C⁻}
      (N : Γ ⊢ C⁻)
      → Γ ∣ [] ⊢ C⁻
    cL : ∀{Q Δ C⁻}
      (N : (Inr Q :: Γ) ∣ Δ ⊢ C⁻)
      → Γ ∣ c Q :: Δ ⊢ C⁻
    ↓L : ∀{A⁻ Δ C⁻}
      (N : (Inl A⁻ :: Γ) ∣ Δ ⊢ C⁻)
      → Γ ∣ ↓ A⁻ :: Δ ⊢ C⁻
    falseE : ∀{Δ C⁻}
      → Γ ∣ false :: Δ ⊢ C⁻
    ⊕L : ∀{A⁺ B⁺ Δ C⁻}
      (N₁ : Γ ∣ A⁺ :: Δ ⊢ C⁻)
      (N₂ : Γ ∣ B⁺ :: Δ ⊢ C⁻)
      → Γ ∣ A⁺ ⊕ B⁺ :: Δ ⊢ C⁻
    trueE : ∀{Δ C⁻}
      (N : Γ ∣ Δ ⊢ C⁻)
      → Γ ∣ true :: Δ ⊢ C⁻
    ⊗L : ∀{A⁺ B⁺ Δ C⁻}
      (N : Γ ∣ A⁺ :: B⁺ :: Δ ⊢ C⁻)
      → Γ ∣ A⁺ ⊗ B⁺ :: Δ ⊢ C⁻

mutual
  wkN : ∀{Γ Γ' A⁻} → Γ ⊆ Γ' → Γ ⊢ A⁻ → Γ' ⊢ A⁻ 
  wkN θ N = {!!} 

  wkNI : ∀{Γ Γ' Δ A⁻} → Γ ⊆ Γ' → Γ ∣ Δ ⊢ A⁻ → Γ' ∣ Δ ⊢ A⁻ 
  wkNI θ N = {!!} 

  wkSp : ∀{Γ Γ' C⁻ A⁻} → Γ ⊆ Γ' → Γ [ A⁻ ]⊢ C⁻ → Γ' [ A⁻ ]⊢ C⁻
  wkSp θ σ = {!!} 

  wkσ : ∀{Γ Γ' Δ} → Γ ⊆ Γ' → Γ ⊢[ Δ ] → Γ' ⊢[ Δ ] 
  wkσ θ σ = {!!} 

mutual
  cut : ∀{Γ A⁻ C⁻} (Γ' : Ctx)
    → Γ ⊢ A⁻
    → (Γ' ++ Inl A⁻ :: Γ) ⊢ C⁻
    → (Γ' ++ Γ) ⊢ C⁻
  cut [] M (foc Z atm Sp) = subst⁻ _ [] M (cutSp [] M Sp) atm
  cut [] M (foc (S x) atm Sp) = foc x atm (cutSp [] M Sp)
  cut (._ :: Γ') M (foc Z atm Sp) = foc Z atm (cutSp (_ :: Γ') M Sp)
  cut (_ :: Γ') M (foc (S x) atm Sp) = {!cut Γ' M (foc !}
  cut Γ' M (↑R σ) = ↑R (cutσ Γ' M σ)
  cut Γ' M ⊤R = ⊤R
  cut Γ' M (&R N₁ N₂) = &R (cut Γ' M N₁) (cut Γ' M N₂)
  cut Γ' M (⊸R N) = ⊸R (cutNI Γ' M N)

  -- Right commutative cases
  cutNI : ∀{Γ A⁻ Δ C⁻} (Γ' : Ctx)
    → Γ ⊢ A⁻
    → (Γ' ++ Inl A⁻ :: Γ) ∣ Δ ⊢ C⁻
    → (Γ' ++ Γ) ∣ Δ ⊢ C⁻
  cutNI Γ' M (nil N) = nil (cut Γ' M N)
  cutNI Γ' M (cL N) = cL (cutNI (_ :: Γ') M N)
  cutNI Γ' M (↓L N) = ↓L (cutNI (_ :: Γ') M N)
  cutNI Γ' M falseE = falseE
  cutNI Γ' M (⊕L N₁ N₂) = ⊕L (cutNI Γ' M N₁) (cutNI Γ' M N₂)
  cutNI Γ' M (trueE N) = trueE (cutNI Γ' M N)
  cutNI Γ' M (⊗L N) = ⊗L (cutNI Γ' M N) 

  cutSp : ∀{Γ A⁻ B⁻ C⁻} (Γ' : Ctx)
    → Γ ⊢ A⁻
    → (Γ' ++ Inl A⁻ :: Γ) [ B⁻ ]⊢ C⁻
    → (Γ' ++ Γ) [ B⁻ ]⊢ C⁻
  cutSp Γ' M nil = nil
  cutSp Γ' M (cont N) = cont (cutNI Γ' M N)
  cutSp Γ' M (&L₁ Sp) = &L₁ (cutSp Γ' M Sp)
  cutSp Γ' M (&L₂ Sp) = &L₂ (cutSp Γ' M Sp)
  cutSp Γ' M (⊸L σ Sp) = ⊸L (cutσ Γ' M σ) (cutSp Γ' M Sp)

  cutσ : ∀{Γ A⁻ Δ} (Γ' : Ctx)
    → Γ ⊢ A⁻
    → (Γ' ++ Inl A⁻ :: Γ) ⊢[ Δ ]
    → (Γ' ++ Γ) ⊢[ Δ ]
  cutσ Γ' M nil = nil
  cutσ Γ' M (cR x σ) = cR {!x!} (cutσ Γ' M σ)
  cutσ Γ' M (↓R N σ) = ↓R (cut Γ' M N) (cutσ Γ' M σ)
  cutσ Γ' M (⊕R₁ σ) = ⊕R₁ (cutσ Γ' M σ)
  cutσ Γ' M (⊕R₂ σ) = ⊕R₂ (cutσ Γ' M σ)
  cutσ Γ' M (trueR σ) = trueR (cutσ Γ' M σ)
  cutσ Γ' M (⊗R σ) = ⊗R (cutσ Γ' M σ)

  -- Left commutative cases
  cuto : ∀{Γ Δ Δ' C}
    → Γ ∣ Δ' ⊢ ↑ Δ
    → Γ ∣ Δ ⊢ C
    → Γ ∣ Δ' ⊢ C
  cuto (nil M) N = nil (cutl M N)
  cuto (cL M) N = cL ? -- (cuto M {!!})
  cuto (↓L M) N = ↓L ? -- (cuto M {!!})
  cuto falseE N = falseE
  cuto (⊕L N₁ N₂) N = ⊕L (cuto N₁ N) (cuto N₂ N)
  cuto (trueE M) N = trueE (cuto M N)
  cuto (⊗L M) N = ⊗L (cuto M N)

  cutl : ∀{Γ Δ C}
    → Γ ⊢ ↑ Δ
    → Γ ∣ Δ ⊢ C
    → Γ ⊢ C
  cutl = {!!}

  cutL : ∀{Γ B⁻ Δ C⁻}
    → Γ [ B⁻ ]⊢ ↑ Δ
    → Γ ∣ Δ ⊢ C⁻
    → Γ [ B⁻ ]⊢ C⁻
  cutL (cont M) N = cont (cuto M N)
  cutL (&L₁ Sp) N = &L₁ (cutL Sp N)
  cutL (&L₂ Sp) N = &L₂ (cutL Sp N)
  cutL (⊸L σ Sp) N = ⊸L {!!} (cutL Sp N)

  subst⁻ : ∀{ Γ C⁻} (A⁻ : _) (Γ' : Ctx)
    → Γ ⊢ A⁻
    → (Γ' ++ Γ) [ A⁻ ]⊢ C⁻
    → Atomic C⁻
    → (Γ' ++ Γ) ⊢ C⁻
  subst⁻ (c Q) Γ' (foc x atm Sp) nil a = wkN {!!} (foc x atm Sp)
  subst⁻ (↑ Δ) Γ' (foc x atm Sp) (cont N) a = 
    {!!} -- foc (LIST.SET.sub-appendl _ Γ' x) a (cutL (wkSp {!!} Sp) N)
  subst⁻ (↑ Δ) Γ' (↑R σ) (cont N) a = {!!} -- subst⁺ (wkσ {!!} σ) N 
  subst⁻ ⊤ Γ' M () a
  subst⁻ (A⁻ & B⁻) Γ' (foc x () Sp) M a
  subst⁻ (A⁻ & B⁻) Γ' (&R N₁ N₂) (&L₁ Sp) a = subst⁻ A⁻ Γ' N₁ Sp a
  subst⁻ (A⁻ & B⁻) Γ' (&R N₁ N₂) (&L₂ Sp) a = subst⁻ B⁻ Γ' N₂ Sp a
  subst⁻ (Δ ⊸ B⁻) Γ' (foc x () Sp) Sp' a
  subst⁻ (Δ ⊸ B⁻) Γ' (⊸R N) (⊸L σ Sp) a = 
    subst⁻ B⁻ Γ' (subst⁺ [] (wkσ {!!} σ) N) Sp a
 
  subst⁺ : ∀{Γ Δ C⁻} (Γ' : Ctx)
    → Γ ⊢[ Δ ]
    → (Γ' ++ Γ) ∣ Δ ⊢ C⁻
    → (Γ' ++ Γ) ⊢ C⁻
  subst⁺ Γ' nil (nil N) = N
  subst⁺ Γ' (cR x σ) (cL N) = subst⁺ Γ' σ (wkNI {!!} N)
  subst⁺ Γ' (↓R M σ) (↓L N) = subst⁺ Γ' σ (cutNI [] (wkN {!!} M) N) 
  subst⁺ Γ' (⊕R₁ σ) (⊕L N₁ N₂) = subst⁺ Γ' σ N₁
  subst⁺ Γ' (⊕R₂ σ) (⊕L N₁ N₂) = subst⁺ Γ' σ N₂
  subst⁺ Γ' (trueR σ) (trueE N) = subst⁺ Γ' σ N
  subst⁺ Γ' (⊗R σ) (⊗L N) = subst⁺ Γ' σ N

{-
  subst⁻ Γ' M (⇑⇓ R) = {!!}
  subst⁻ Γ' M (↑I σ) = ↑I (subst⁺ Γ' M σ)
  subst⁻ Γ' M (↑E atm R N) = ↑E atm {!!} (substinv Γ' M N)
  subst⁻ Γ' M ⊤I = ⊤I
  subst⁻ Γ' M (&I N₁ N₂) = &I (subst⁻ Γ' M N₁) (subst⁻ Γ' M N₂)
  subst⁻ Γ' M (⊸I N) = ⊸I (substinv Γ' M N)

  substinv : ∀{Γ A⁻ Δ C⁻} (Γ' : Ctx)
    → Γ ⊢ A⁻ verif
    → (Γ' ++ Inl A⁻ :: Γ) ∣ Δ ⊢ C⁻ verif
    → (Γ' ++ Γ) ∣ Δ ⊢ C⁻ verif
  substinv Γ' M (nil N) = nil (subst⁻ Γ' M N)
  substinv Γ' M (cE N) = cE (substinv (_ :: Γ') M N)
  substinv Γ' M (↓E N) = ↓E (substinv (_ :: Γ') M N)
  substinv Γ' M falseE = falseE
  substinv Γ' M (⊕E N₁ N₂) = ⊕E (substinv Γ' M N₁) (substinv Γ' M N₂)
  substinv Γ' M (trueE N) = trueE (substinv Γ' M N)
  substinv Γ' M (⊗E N) = ⊗E (substinv Γ' M N)

  subst⁺ : ∀{Γ A⁻ Δ} (Γ' : Ctx)
    → Γ ⊢ A⁻ verif
    → (Γ' ++ Inl A⁻ :: Γ) ⊢ Δ subst
    → (Γ' ++ Γ) ⊢ Δ subst
  subst⁺ Γ' M nil = nil
  subst⁺ Γ' M (cI x σ) = cI {!x!} (subst⁺ Γ' M σ)
  subst⁺ Γ' M (↓I N σ) = ↓I (subst⁻ Γ' M N) (subst⁺ Γ' M σ)
  subst⁺ Γ' M (⊕I₁ σ) = ⊕I₁ (subst⁺ Γ' M σ)
  subst⁺ Γ' M (⊕I₂ σ) = ⊕I₂ (subst⁺ Γ' M σ)
  subst⁺ Γ' M (trueI σ) = trueI (subst⁺ Γ' M σ)
  subst⁺ Γ' M (⊗I σ) = ⊗I (subst⁺ Γ' M σ)

--  substR : ∀{Γ A⁻ C⁻}
--    → Γ ⊢ A⁻ verif
--    → Γ' ++ Inl  
  


  substσ : ∀{Γ Δ C⁻} → Γ ⊢ Δ subst → Γ ∣ Δ ⊢ C⁻ verif → Γ ⊢ C⁻ verif
  substσ nil (nil N) = N
  substσ (cI x τ) (cE N) = substσ τ (wkNI (LIST.SET.sub-cntr x) N)
  substσ (↓I M τ) (↓E N) = substσ τ (substinv [] M N)
  substσ (⊕I₁ τ) (⊕E N₁ N₂) = substσ τ N₁
  substσ (⊕I₂ τ) (⊕E N₁ N₂) = substσ τ N₂
  substσ (trueI τ) (trueE N) = substσ τ N
  substσ (⊗I τ) (⊗E N) = substσ τ N
-}