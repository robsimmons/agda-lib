open import Prelude hiding (⊤)

module Polar where

data Pol : Set where
  ⁻ : Pol
  ⁺ : Pol  
 
data Type : Pol → Set where
  c : {⁼ : Pol} → String → Type ⁼
  ↓ : Type ⁻ → Type ⁺
  ↑ : List (Type ⁺) → Type ⁻
  false : Type ⁺ 
  _⊕_ : Type ⁺ → Type ⁺ → Type ⁺ 
  true : Type ⁺
  _⊗_ : Type ⁺ → Type ⁺ → Type ⁺
  ⊤ : Type ⁻
  _&_ : Type ⁻ → Type ⁻ → Type ⁻
  _⊸_ : List (Type ⁺) → Type ⁻ → Type ⁻

data Atomic : Type ⁻ → Set where
  c : ∀{Q} → Atomic (c Q)
  ↑ : ∀{A⁺} → Atomic (↑ A⁺)

Ctx = List (Type ⁻ + String)

_⊆_ : Ctx → Ctx → Set
_⊆_ = LIST.SET.Sub

mutual
  data _⊢_verif (Γ : Ctx) : Type ⁻ → Set where
    ⇑⇓ : ∀{Q}
      (R : Γ ⊢ c Q use)
      → Γ ⊢ c Q verif
    ↑I : ∀{Δ}
      (σ : Γ ⊢ Δ subst)
      → Γ ⊢ ↑ Δ verif
    ↑E : ∀{γ Δ} 
      (atm : Atomic γ)
      (R : Γ ⊢ ↑ Δ use)
      (N : Γ ∣ Δ ⊢ γ verif)
      → Γ ⊢ γ verif
    ⊤I : Γ ⊢ ⊤ verif
    &I : ∀{A⁻ B⁻}
      (N₁ : Γ ⊢ A⁻ verif)
      (N₂ : Γ ⊢ B⁻ verif)
      → Γ ⊢ A⁻ & B⁻ verif
    ⊸I : ∀{Δ B⁻}
      (N : Γ ∣ Δ ⊢ B⁻ verif)
      → Γ ⊢ Δ ⊸ B⁻ verif
  
  data _⊢_use (Γ : Ctx) : Type ⁻ → Set where
    var : ∀{A⁻}
      (x : Inl A⁻ ∈ Γ) 
      → Γ ⊢ A⁻ use
    &E₁ : ∀{A⁻ B⁻}
      (F : Γ ⊢ A⁻ & B⁻ use)
      → Γ ⊢ A⁻ use
    &E₂ : ∀{A⁻ B⁻}
      (F : Γ ⊢ A⁻ & B⁻ use)
      → Γ ⊢ B⁻ use
    ⊸E : ∀{Δ B⁻}
      (R : Γ ⊢ Δ ⊸ B⁻ use)
      (σ : Γ ⊢ Δ subst)
      → Γ ⊢ B⁻ use

  data _⊢_subst (Γ : Ctx) : List (Type ⁺) → Set where
    nil : Γ ⊢ [] subst
    cI : ∀{Q Δ}
      (x : Inr Q ∈ Γ)
      (σ : Γ ⊢ Δ subst)
      → Γ ⊢ c Q :: Δ subst
    ↓I : ∀{A⁻ Δ}
      (N : Γ ⊢ A⁻ verif)
      (σ : Γ ⊢ Δ subst)
      → Γ ⊢ ↓ A⁻ :: Δ subst
    ⊕I₁ : ∀{A⁺ B⁺ Δ}
      (σ : Γ ⊢ A⁺ :: Δ subst)
      → Γ ⊢ A⁺ ⊕ B⁺ :: Δ subst
    ⊕I₂ : ∀{A⁺ B⁺ Δ}
      (σ : Γ ⊢ B⁺ :: Δ subst)
      → Γ ⊢ A⁺ ⊕ B⁺ :: Δ subst
    trueI : ∀{Δ}
      (σ : Γ ⊢ Δ subst)
      → Γ ⊢ true :: Δ subst
    ⊗I : ∀{A⁺ B⁺ Δ}
      (σ : Γ ⊢ A⁺ :: B⁺ :: Δ subst)
      → Γ ⊢ A⁺ ⊗ B⁺ :: Δ subst

  data _∣_⊢_verif (Γ : Ctx) : List (Type ⁺) → Type ⁻ → Set where
    nil : ∀{C⁻}
      (N : Γ ⊢ C⁻ verif)
      → Γ ∣ [] ⊢ C⁻ verif
    cE : ∀{Q Δ C⁻}
      (N : (Inr Q :: Γ) ∣ Δ ⊢ C⁻ verif)
      → Γ ∣ c Q :: Δ ⊢ C⁻ verif
    ↓E : ∀{A⁻ Δ C⁻}
      (N : (Inl A⁻ :: Γ) ∣ Δ ⊢ C⁻ verif)
      → Γ ∣ ↓ A⁻ :: Δ ⊢ C⁻ verif
    falseE : ∀{Δ C⁻}
      → Γ ∣ false :: Δ ⊢ C⁻ verif
    ⊕E : ∀{A⁺ B⁺ Δ C⁻}
      (N₁ : Γ ∣ A⁺ :: Δ ⊢ C⁻ verif)
      (N₂ : Γ ∣ B⁺ :: Δ ⊢ C⁻ verif)
      → Γ ∣ A⁺ ⊕ B⁺ :: Δ ⊢ C⁻ verif
    trueE : ∀{Δ C⁻}
      (N : Γ ∣ Δ ⊢ C⁻ verif)
      → Γ ∣ true :: Δ ⊢ C⁻ verif
    ⊗E : ∀{A⁺ B⁺ Δ C⁻}
      (N : Γ ∣ A⁺ :: B⁺ :: Δ ⊢ C⁻ verif)
      → Γ ∣ A⁺ ⊗ B⁺ :: Δ ⊢ C⁻ verif

mutual
  wkN : ∀{Γ Γ' A⁻} → Γ ⊆ Γ' → Γ ⊢ A⁻ verif → Γ' ⊢ A⁻ verif
  wkN θ N = {!!} 

  wkNI : ∀{Γ Γ' Δ A⁻} → Γ ⊆ Γ' → Γ ∣ Δ ⊢ A⁻ verif → Γ' ∣ Δ ⊢ A⁻ verif
  wkNI θ N = {!!} 

mutual
  subst⁻ : ∀{Γ A⁻ C⁻} (Γ' : Ctx)
    → Γ ⊢ A⁻ verif
    → (Γ' ++ Inl A⁻ :: Γ) ⊢ C⁻ verif
    → (Γ' ++ Γ) ⊢ C⁻ verif
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