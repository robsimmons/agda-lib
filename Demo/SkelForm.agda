{- "Skeleton form" for the simply typed lambda calculus with products -}

open import Prelude

module Demo.SkelForm where

infixr 5 _⊃_
infixr 4 _∧_
data Type : Set where
   con : String → Type
   _⊃_ : Type → Type → Type
   _∧_ : Type → Type → Type

Ctx = List Type
MCtx = List Ctx

_⊆_ : Ctx → Ctx → Set
_⊆_ = LIST.SET.Sub

module EXTERNAL (sig : String → Maybe Type) where
   infixl 5 _·_
   data Term (Δ : Ctx) (Γ : Ctx) : Type → Set where
      mvar : ∀{A} → A ∈ Δ → Term Δ Γ A
      var : ∀{A} → A ∈ Γ → Term Δ Γ A
      con : (c : String) {ch : Check (isSome (sig c))}
         → Term Δ Γ (valOf (sig c) {ch})
      _·_ : ∀{A B} → Term Δ Γ (A ⊃ B) → Term Δ Γ A → Term Δ Γ B
      Λ : ∀{A B} → Term Δ (A :: Γ) B → Term Δ Γ (A ⊃ B)

module TEST where
   sig : String → Maybe Type
   sig "lam" = Just ((con "exp" ⊃ con "exp") ⊃ con "exp")
   sig "app" = Just (con "exp" ⊃ con "exp" ⊃ con "exp")
   sig _ = Nothing

   open EXTERNAL sig public

   combI : Term [] [] (con "exp")
   combI = con "lam" · Λ (var Z)
   
   combK : Term [] [] (con "exp")
   combK = con "lam" · Λ (con "lam" · Λ (var (S Z)))
 
   combS : Term [] [] (con "exp")
   combS = 
      con "lam" · Λ (con "lam" · Λ (con "lam" · Λ 
       (con "app" · 
         (con "app" · var (S (S Z)) · var Z) · 
         (con "app" · var (S Z) · var Z))))


module RAISED (sig : String → Maybe Type) where
   data Head (Γ : Ctx) : Type → Set where
      var : ∀{A} (n : A ∈ Γ) → Head Γ A
      con : (c : String) {ch : Check (isSome (sig c))}
         → Head Γ (valOf (sig c) {ch})

   infixr 20 _·_
   mutual
      data Term (Γ : Ctx) : Type → Set where
         _·_ : ∀{A Q}
            (x : Head Γ A)
            (sk : Spine Γ A (con Q))
            → Term Γ (con Q)
         Λ : ∀{A B}
            (n : Term (A :: Γ) B)
            → Term Γ (A ⊃ B)
         ⟨_,_⟩ : ∀{A B}
            (n₁ : Term Γ A)
            (n₂ : Term Γ B)
            → Term Γ (A ⊃ B)
         
      data Spine (Γ : Ctx) : Type → Type → Set where
         ⟨⟩ : ∀{A} → Spine Γ A A
         _·_ : ∀{A B C} 
            (n : Term Γ A)
            (sp : Spine Γ B C)
            → Spine Γ (A ⊃ B) C         
         π₁ : ∀{A B C}
            (sp : Spine Γ A C)
            → Spine Γ (A ∧ B) C
         π₂ : ∀{A B C}
            (sp : Spine Γ B C)
            → Spine Γ (A ∧ B) C

module LOWERED (sig : String → Maybe Type) where
   data Head (Γ : Ctx) : Type → Set where
      var : ∀{A} (n : A ∈ Γ) → Head Γ A
      con : (c : String) {ch : Check (isSome (sig c))}
         → Head Γ (valOf (sig c) {ch})

   data Skel (Γ : Ctx) : Type → Ctx → Type → Set where
      ⟨⟩ : ∀{A} → Skel Γ A Γ A
      ·_ : ∀{A B Γ' C}
         (sk : Skel (A :: Γ) B Γ' C)
         → Skel Γ (A ⊃ B) Γ' C
      π₁ : ∀{A B Γ' C}
         (sk : Skel Γ A Γ' C)
         → Skel Γ (A ∧ B) Γ' C
      π₂ : ∀{A B Γ' C}
         (sk : Skel Γ B Γ' C)
         → Skel Γ (A ∧ B) Γ' C
      
   infixr 20 _·_[_]
   mutual
      -- σ : Subst Γ Γ' is the typing derivation Γ' ⊢ σ : Γ
      data Subst : Ctx → Ctx → Set where
         ↑ : ∀{Γ} (Γ' : Ctx) → Subst (Γ' ++ Γ) Γ
         _,_ : ∀{Γ Γ' A} (n : Term Γ' A) (σ : Subst Γ Γ') → Subst (A :: Γ) Γ'
 
      -- n : Term Γ A is the typing derivation Γ ⊢ n : A
      data Term (Γ : Ctx) : Type → Set where
         _·_[_] : ∀{A Q Γ'}
            (x : Head Γ A)
            (sk : Skel Γ A Γ' (con Q))
            (σ : Subst Γ' Γ)
            → Term Γ (con Q)
         Λ : ∀{A B}
            (n : Term (A :: Γ) B)
            → Term Γ (A ⊃ B)
         ⟨_,_⟩ : ∀{A B}
            (n₁ : Term Γ A)
            (n₂ : Term Γ B)
            → Term Γ (A ⊃ B)
         
      data Spine (Γ : Ctx) : Type → Type → Set where
         ⟨⟩ : ∀{A} → Spine Γ A A
         _·_ : ∀{A B C} 
            (n : Term Γ A)
            (sp : Spine Γ B C)
            → Spine Γ (A ⊃ B) C         
         π₁ : ∀{A B C}
            (sp : Spine Γ A C)
            → Spine Γ (A ∧ B) C
         π₂ : ∀{A B C}
            (sp : Spine Γ B C)
            → Spine Γ (A ∧ B) C
         