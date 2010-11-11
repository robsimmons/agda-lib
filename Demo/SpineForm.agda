{- The canonical forms of the simply typed lambda calculus -}

module Demo.SpineForm where

open import Prelude

postulate String : Set
{-# BUILTIN STRING String #-}
{-# COMPILED_TYPE String String #-}

infixr 5 _⊃_
data Type : Set where
   con : String → Type
   _⊃_ : Type → Type → Type

Ctx = List Type

_⊆_ : Ctx → Ctx → Set
_⊆_ = LIST.SET.Sub

module SPINEFORM (sig : String → Maybe Type) where
   data Head (Γ : Ctx) : Type → Set where
      var : ∀{A} (n : A ∈ Γ) → Head Γ A
      con : (c : String) {ch : Check (isSome (sig c))}
         → Head Γ (valOf (sig c) {ch})

   {- Terms -}
   infixr 20 _·_
   mutual 
      data Term (Γ : Ctx) : Type → Set where
         _·_ : ∀{A Q}
            (x : Head Γ A)
            (sp : Spine Γ A (con Q))
            → Term Γ (con Q)
         Λ : ∀{A B}
            (n : Term (A :: Γ) B)
            → Term Γ (A ⊃ B)

      data Spine (Γ : Ctx) : Type → Type → Set where
         ⟨⟩ : ∀{A} → Spine Γ A A
         _·_ : ∀{A B C} 
            (n : Term Γ A)
            (sp : Spine Γ B C)
            → Spine Γ (A ⊃ B) C         

   {- Terms with a metric -}
   data Metric : Set where
      ○ : Metric
      _●_ : Metric → Metric → Metric
      > : Metric → Metric

   mutual
      data MTerm (Γ : Ctx) : Type → Metric → Set where
         _·_ : ∀{A Q m}
            (x : Head Γ A)
            (sp : MSpine Γ A (con Q) m)
            → MTerm Γ (con Q) (> m)
         Λ : ∀{A B m}
            (n : MTerm (A :: Γ) B m)
            → MTerm Γ (A ⊃ B) (> m)

      data MSpine (Γ : Ctx) : Type → Type → Metric → Set where
         ⟨⟩ : ∀{A} → MSpine Γ A A ○
         _·_ : ∀{A B C m1 m2} 
            (n : MTerm Γ A m1)
            (sp : MSpine Γ B C m2)
            → MSpine Γ (A ⊃ B) C (m1 ● m2)         
  
   {- Into and out of the metric -}
   mutual
      tm→ : ∀{Γ A m} → MTerm Γ A m → Term Γ A
      tm→ (x · sp) = x · sp→ sp
      tm→ (Λ n) = Λ (tm→ n)

      sp→ : ∀{Γ A C m} → MSpine Γ A C m → Spine Γ A C
      sp→ ⟨⟩ = ⟨⟩
      sp→ (n · sp) = tm→ n · sp→ sp

   mutual
      →tm : ∀{Γ A} → Term Γ A → ∃ λ m → MTerm Γ A m
      →tm (x · sp) = , x · snd (→sp sp)
      →tm (Λ n) = , Λ (snd (→tm n))

      →sp : ∀{Γ A C} → Spine Γ A C → ∃ λ m → MSpine Γ A C m
      →sp ⟨⟩ = , ⟨⟩
      →sp (n · sp) = , snd (→tm n) · snd (→sp sp)
    
   {- Weakening in and out of the metric -}
   mutual
      wkN : ∀{Γ Δ A} → Γ ⊆ Δ → Term Γ A → Term Δ A
      wkN θ (var n · sp) = var (θ n) · wkS θ sp
      wkN θ (con c · sp) = con c · wkS θ sp
      wkN θ (Λ n) = Λ (wkN (LIST.SET.sub-cons-congr θ) n)

      wkS : ∀{Γ Δ A C} → Γ ⊆ Δ → Spine Γ A C → Spine Δ A C
      wkS θ ⟨⟩ = ⟨⟩
      wkS θ (n · sp) = wkN θ n · wkS θ sp

   mutual
      wkMN : ∀{Γ Δ A m} → Γ ⊆ Δ → MTerm Γ A m → MTerm Δ A m
      wkMN θ (var n · sp) = var (θ n) · wkMS θ sp
      wkMN θ (con c · sp) = con c · wkMS θ sp
      wkMN θ (Λ n) = Λ (wkMN (LIST.SET.sub-cons-congr θ) n)

      wkMS : ∀{Γ Δ A C m} → Γ ⊆ Δ → MSpine Γ A C m → MSpine Δ A C m
      wkMS θ ⟨⟩ = ⟨⟩
      wkMS θ (n · sp) = wkMN θ n · wkMS θ sp
  
   {- Specific instances of weakening -} 
   wken : ∀{Γ A C} → Term Γ C → Term (A :: Γ) C
   wken = wkN LIST.SET.sub-wken

   exch : ∀{Γ A B C} → Term (A :: B :: Γ) C → Term (B :: A :: Γ) C
   exch = wkN LIST.SET.sub-exch

   wkex : ∀{Γ A B C} → Term (A :: Γ) C → Term (A :: B :: Γ) C
   wkex = wkN LIST.SET.sub-wkex

   wkenM : ∀{Γ A C m} → MTerm Γ C m → MTerm (A :: Γ) C m
   wkenM = wkMN LIST.SET.sub-wken

   exchM : ∀{Γ A B C m} → MTerm (A :: B :: Γ) C m → MTerm (B :: A :: Γ) C m
   exchM = wkMN LIST.SET.sub-exch

   wkexM : ∀{Γ A B C m} → MTerm (A :: Γ) C m → MTerm (A :: B :: Γ) C m
   wkexM = wkMN LIST.SET.sub-wkex
   
   {- Substitution -}
   mutual 
      substM : ∀{Γ A C m} → Term Γ A → MTerm (A :: Γ) C m → Term Γ C
      substM n1 (var Z · sp) = hred n1 (substSP n1 sp)
      substM n1 (var (S n) · sp) = var n · substSP n1 sp
      substM n1 (con c · sp) = con c · substSP n1 sp
      substM n1 (Λ n) = Λ (substM (wken n1) (exchM n)) 

      substSP : ∀{Γ A B C m} → Term Γ A → MSpine (A :: Γ) B C m → Spine Γ B C
      substSP n1 ⟨⟩ = ⟨⟩
      substSP n1 (n · sp) = substM n1 n · substSP n1 sp

      hred :  ∀{Γ A Q} 
         → Term Γ A 
         → Spine Γ A (con Q) 
         → Term Γ (con Q)
      hred (x · sp) ⟨⟩ = x · sp
      hred (Λ n) (n' · sp) = hred (substM n' (snd (→tm n))) sp

   subst : ∀{Γ A C} → Term Γ A → Term (A :: Γ) C → Term Γ C
   subst n1 n2 = substM n1 (snd (→tm n2))

module TEST where
   sig : String → Maybe Type
   sig "lam" = Inl ((con "exp" ⊃ con "exp") ⊃ con "exp")
   sig "app" = Inl (con "exp" ⊃ con "exp" ⊃ con "exp")
   sig _ = Inr <>

   open SPINEFORM sig public
   
   combI : Term [] (con "exp")
   combI = con "lam" · Λ (var Z · ⟨⟩) · ⟨⟩

   combK : Term [] (con "exp")
   combK = con "lam" · Λ (con "lam" · Λ (var (S Z) · ⟨⟩) · ⟨⟩) · ⟨⟩

   combS : Term [] (con "exp")
   combS = con "lam" · Λ (con "lam" · Λ (con "lam" · Λ 
      (con "app" · 
       (con "app" · (var (S (S Z)) · ⟨⟩) · (var Z · ⟨⟩) · ⟨⟩) · 
       (con "app" · (var (S Z) · ⟨⟩) · (var Z · ⟨⟩) · ⟨⟩) · ⟨⟩) · ⟨⟩) · ⟨⟩) · ⟨⟩
