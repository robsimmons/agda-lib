{- "Skeleton form" for the simply typed lambda calculus with products -}

-- Too lazy for metrics, we're switching to %trustme
{-# OPTIONS --no-termination-check #-}

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

open LIST.SET
_⊆_ : Ctx → Ctx → Set
_⊆_ = Sub

module EXTERNAL (sig : String → Maybe Type) where
   infixl 5 _·_
   data Term (Δ : Ctx) (Γ : Ctx) : Type → Set where
      var : ∀{A} (x : A ∈ Γ) → Term Δ Γ A
      mvar : ∀{A} (x : A ∈ Δ) → Term Δ Γ A
      con : (c : String) {ch : Check (isSome (sig c))}
         → Term Δ Γ (valOf (sig c) {ch})
      _·_ : ∀{A B} (n₁ : Term Δ Γ (A ⊃ B)) (n₂ : Term Δ Γ A) → Term Δ Γ B
      Λ : ∀{A B} (n : Term Δ (A :: Γ) B) → Term Δ Γ (A ⊃ B)

   -- Simultaneous (modal) substitution
   SSubst : Ctx → Ctx → Set 
   SSubst Δ Δ' = LIST.All (Term Δ' []) Δ

   postulate ssubst : ∀{Δ Δ' Γ A} → SSubst Δ Δ' → Term Δ Γ A → Term Δ' Γ A
 
   -- POSSIBLE: give a notion of equivalence (βη) for this language

module RAISED (sig : String → Maybe Type) where
   data Head (Δ Γ : Ctx) : Type → Set where
      var : ∀{A} (n : A ∈ Γ) → Head Δ Γ A
      mvar : ∀{A} (n : A ∈ Δ) → Head Δ Γ A
      con : (c : String) {ch : Check (isSome (sig c))}
         → Head Δ Γ (valOf (sig c) {ch})

   infixr 20 _·_
   mutual
      data Term (Δ Γ : Ctx) : Type → Set where
         _·_ : ∀{A Q}
            (x : Head Δ Γ A)
            (sp : Spine Δ Γ A (con Q))
            → Term Δ Γ (con Q)
         Λ : ∀{A B}
            (n : Term Δ (A :: Γ) B)
            → Term Δ Γ (A ⊃ B)
         ⟨_,_⟩ : ∀{A B}
            (n₁ : Term Δ Γ A)
            (n₂ : Term Δ Γ B)
            → Term Δ Γ (A ∧ B)
         
      data Spine (Δ Γ : Ctx) : Type → Type → Set where
         ⟨⟩ : ∀{A} → Spine Δ Γ A A
         _·_ : ∀{A B C} 
            (n : Term Δ Γ A)
            (sp : Spine Δ Γ B C)
            → Spine Δ Γ (A ⊃ B) C         
         π₁ : ∀{A B C}
            (sp : Spine Δ Γ A C)
            → Spine Δ Γ (A ∧ B) C
         π₂ : ∀{A B C}
            (sp : Spine Δ Γ B C)
            → Spine Δ Γ (A ∧ B) C

   mutual 
      wk : ∀{Δ Γ Γ' A} → Γ ⊆ Γ' → Term Δ Γ A → Term Δ Γ' A
      wk θ (h · sp) = wkH θ h · wkS θ sp
      wk θ (Λ n) = Λ (wk (LIST.SET.sub-cons-congr θ) n)
      wk θ ⟨ n₁ , n₂ ⟩ = ⟨ wk θ n₁ , wk θ n₂ ⟩

      wkH : ∀{Δ Γ Γ' A} → Γ ⊆ Γ' → Head Δ Γ A → Head Δ Γ' A
      wkH θ (var n) = var (θ n)
      wkH θ (mvar n) = mvar n
      wkH θ (con c) = con c

      wkS : ∀{Δ Γ Γ' A C} → Γ ⊆ Γ' → Spine Δ Γ A C → Spine Δ Γ' A C
      wkS θ ⟨⟩ = ⟨⟩
      wkS θ (n · sp) = wk θ n · wkS θ sp
      wkS θ (π₁ sp) = π₁ (wkS θ sp)
      wkS θ (π₂ sp) = π₂ (wkS θ sp)
   
   mutual 
      subst : ∀{Δ Γ A C} → Term Δ Γ A → Term Δ (A :: Γ) C → Term Δ Γ C
      subst n1 (var Z · sp) = hred n1 (substS n1 sp)
      subst n1 (var (S n) · sp) = var n · substS n1 sp
      subst n1 (mvar n · sp) = mvar n · substS n1 sp
      subst n1 (con c · sp) = con c · substS n1 sp
      subst n1 (Λ n) = Λ (subst (wk sub-wken n1) (wk sub-exch n))
      subst n1 ⟨ n₁ , n₂ ⟩ = ⟨ subst n1 n₁ , subst n1 n₂ ⟩

      substS : ∀{Δ Γ A B C} → Term Δ Γ A → Spine Δ (A :: Γ) B C → Spine Δ Γ B C
      substS n1 ⟨⟩ = ⟨⟩
      substS n1 (n · sp) = subst n1 n · substS n1 sp
      substS n1 (π₁ sp) = π₁ (substS n1 sp)
      substS n1 (π₂ sp) = π₂ (substS n1 sp)

      hred : ∀{Δ Γ A C} → Term Δ Γ A → Spine Δ Γ A C → Term Δ Γ C
      hred n ⟨⟩ = n
      hred (Λ n) (n' · sp) = hred (subst n' n) sp
      hred ⟨ n₁ , n₂ ⟩ (π₁ sp) = hred n₁ sp
      hred ⟨ n₁ , n₂ ⟩ (π₂ sp) = hred n₂ sp

   mutual 
      eta : ∀{Δ Γ A} (B : Type) → Head Δ Γ A → Spine Δ Γ A B → Term Δ Γ B
      eta (con y) h sp = h · sp
      eta (A ⊃ B) h sp = 
         Λ (eta B (wkH sub-wken h) 
            (fuse (wkS sub-wken sp) (eta A (var Z) ⟨⟩ · ⟨⟩)))
      eta (A ∧ B) h sp = 
         ⟨ eta A h (fuse sp (π₁ ⟨⟩)) , eta B h (fuse sp (π₂ ⟨⟩)) ⟩

      fuse : ∀{Δ Γ A B C} → Spine Δ Γ A B → Spine Δ Γ B C → Spine Δ Γ A C
      fuse ⟨⟩ sp2 = sp2
      fuse (n · sp) sp2 = n · fuse sp sp2
      fuse (π₁ sp) sp2 = π₁ (fuse sp sp2)
      fuse (π₂ sp) sp2 = π₂ (fuse sp sp2)

   SSubst : Ctx → Ctx → Set 
   SSubst Δ Δ' = LIST.All (Term Δ' []) Δ

   postulate ssubst : ∀{Δ Δ' Γ A} → SSubst Δ Δ' → Term Δ Γ A → Term Δ' Γ A

   open EXTERNAL sig renaming (Term to ExTerm ; SSubst to ExSSubst)
   mutual
      canonize : ∀{Δ Γ A} → ExTerm Δ Γ A → Term Δ Γ A
      canonize (var x) = eta _ (var x) ⟨⟩
      canonize (mvar x) = eta _ (mvar x) ⟨⟩
      canonize (con c {prf}) = eta _ (con c {prf}) ⟨⟩
      canonize (n₁ · n₂) = hred (canonize n₁) (canonize n₂ · ⟨⟩)
      canonize (Λ n) = Λ (canonize n)

   -- substitution should commute with canonization

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
         

module TEST where
   sig : String → Maybe Type
   sig "lam" = Just ((con "exp" ⊃ con "exp") ⊃ con "exp")
   sig "app" = Just (con "exp" ⊃ con "exp" ⊃ con "exp")
   sig _ = Nothing

   open EXTERNAL sig public
   open RAISED sig public using (canonize)

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

