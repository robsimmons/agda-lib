{- The canonical forms of the simply typed lambda calculus in spine form -}

module Demo.SpineForm where

open import Prelude

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
   wkM : ∀{Γ Δ A m} → Γ ⊆ Δ → MTerm Γ A m → MTerm Δ A m
   wkM = wkN 
    where
     mutual 
      wkN : ∀{Γ Δ A m} → Γ ⊆ Δ → MTerm Γ A m → MTerm Δ A m
      wkN θ (var n · sp) = var (θ n) · wkS θ sp
      wkN θ (con c · sp) = con c · wkS θ sp
      wkN θ (Λ n) = Λ (wkN (LIST.SET.sub-cons-congr θ) n)

      wkS : ∀{Γ Δ A C m} → Γ ⊆ Δ → MSpine Γ A C m → MSpine Δ A C m
      wkS θ ⟨⟩ = ⟨⟩
      wkS θ (n · sp) = wkN θ n · wkS θ sp

   wk : ∀{Γ Δ A} → Γ ⊆ Δ → Term Γ A → Term Δ A 
   wk θ n = tm→ (wkM θ (snd (→tm n)))

   {- Specific instances of weakening -} 
   wken : ∀{Γ A C} → Term Γ C → Term (A :: Γ) C
   wken = wk LIST.SET.sub-wken

   exch : ∀{Γ A B C} → Term (A :: B :: Γ) C → Term (B :: A :: Γ) C
   exch = wk LIST.SET.sub-exch

   wkex : ∀{Γ A B C} → Term (A :: Γ) C → Term (A :: B :: Γ) C
   wkex = wk LIST.SET.sub-wkex

   wkenM : ∀{Γ A C m} → MTerm Γ C m → MTerm (A :: Γ) C m
   wkenM = wkM LIST.SET.sub-wken

   exchM : ∀{Γ A B C m} → MTerm (A :: B :: Γ) C m → MTerm (B :: A :: Γ) C m
   exchM = wkM LIST.SET.sub-exch

   wkexM : ∀{Γ A B C m} → MTerm (A :: Γ) C m → MTerm (A :: B :: Γ) C m
   wkexM = wkM LIST.SET.sub-wkex
   
   {- Substitution -}
   substM : ∀{Γ A C m} → Term Γ A → MTerm (A :: Γ) C m → Term Γ C
   substM = substN 
    where
     mutual 
      substN : ∀{Γ A C m} → Term Γ A → MTerm (A :: Γ) C m → Term Γ C
      substN n1 (var Z · sp) = hred n1 (substS n1 sp)
      substN n1 (var (S n) · sp) = var n · substS n1 sp
      substN n1 (con c · sp) = con c · substS n1 sp
      substN n1 (Λ n) = Λ (substN (wken n1) (exchM n)) 

      substS : ∀{Γ A B C m} → Term Γ A → MSpine (A :: Γ) B C m → Spine Γ B C
      substS n1 ⟨⟩ = ⟨⟩
      substS n1 (n · sp) = substN n1 n · substS n1 sp

      hred :  ∀{Γ A Q} 
         → Term Γ A 
         → Spine Γ A (con Q) 
         → Term Γ (con Q)
      hred (x · sp) ⟨⟩ = x · sp
      hred (Λ n) (n' · sp) = hred (substN n' (snd (→tm n))) sp

   subst : ∀{Γ A C} → Term Γ A → Term (A :: Γ) C → Term Γ C
   subst n1 n2 = substM n1 (snd (→tm n2))

   {- Strengthening -}
   stM : ∀{Γ A C m} → MTerm (A :: Γ) C m → Maybe (MTerm Γ C m)
   stM = stN 
    where 
     mutual
      _>>=_ : {A C : Set} → Maybe A → (A → Maybe C) → Maybe C
      _>>=_ = MAYBE.bind

      stN : ∀{Γ A C m} → MTerm (A :: Γ) C m → Maybe (MTerm Γ C m)
      stN (var Z · sp) = MAYBE.fail
      stN (var (S n) · sp) = stS sp >>= λ sp → MAYBE.return (var n · sp)
      stN (con c · sp) = stS sp >>= λ sp' → MAYBE.return (con c · sp')
      stN (Λ n) = stN (exchM n) >>= λ n' → MAYBE.return (Λ n')

      stS : ∀{Γ A B C m} → MSpine (A :: Γ) B C m → Maybe (MSpine Γ B C m)
      stS ⟨⟩ = MAYBE.return ⟨⟩
      stS (n · sp) = 
         stN n >>= λ n' → 
         stS sp >>= λ sp' → 
         MAYBE.return (n' · sp')
  
   st : ∀{Γ A C} → Term (A :: Γ) C → Maybe (Term Γ C)
   st n = MAYBE.bind (stM (snd (→tm n))) (λ n' → MAYBE.return (tm→ n'))

module TEST where
   sig : String → Maybe Type
   sig "lam" = Just ((con "exp" ⊃ con "exp") ⊃ con "exp")
   sig "app" = Just (con "exp" ⊃ con "exp" ⊃ con "exp")
   sig _ = Nothing

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
