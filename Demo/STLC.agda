-- The simply-typed lambda calculus
-- Mentioned here: 
-- requestforlogic.blogspot.com/2010/11/totally-nameless-representation.html

module Demo.STLC where

   open import Prelude

   infixr 5 _⊃_
   data Type : Set where
      con : String → Type
      _⊃_ : Type → Type → Type

   Ctx = List Type

   infixl 5 _·_
   data Term (Γ : Ctx) : Type → Set where
      var : ∀{A} → A ∈ Γ → Term Γ A
      _·_ : ∀{A B} → Term Γ (A ⊃ B) → Term Γ A → Term Γ B
      Λ : ∀{A B} → Term (A :: Γ) B → Term Γ (A ⊃ B)

   data Metric : Set where
      ○ : Metric
      _●_ : Metric → Metric → Metric
      > : Metric → Metric

   data MTerm (Γ : Ctx) : Type → Metric → Set where
      var : ∀{A} → A ∈ Γ → MTerm Γ A ○
      _·_ : ∀{A B m m'} → MTerm Γ (A ⊃ B) m → MTerm Γ A m' → MTerm Γ B (m ● m')
      Λ : ∀{A B m} → MTerm (A :: Γ) B m → MTerm Γ (A ⊃ B) (> m)

   -- Into and out of the metric
   tm→ : ∀{Γ A m} → MTerm Γ A m → Term Γ A
   tm→ (var n) = var n
   tm→ (n1 · n2) = tm→ n1 · tm→ n2
   tm→ (Λ n) = Λ (tm→ n)

   →tm : ∀{Γ A} → Term Γ A → ∃ λ m → MTerm Γ A m
   →tm (var n) = , var n
   →tm (n1 · n2) = , snd (→tm n1) · snd (→tm n2)
   →tm (Λ n) = , Λ (snd (→tm n))

   _⊆_ : Ctx → Ctx → Set
   _⊆_ = LIST.SET.Sub

   -- Weakening inside the metric
   wkM : ∀{Γ Δ A m} → Γ ⊆ Δ → MTerm Γ A m → MTerm Δ A m
   wkM θ (var n) = var (θ n)
   wkM θ (n · n') = wkM θ n · wkM θ n'
   wkM θ (Λ n) = Λ (wkM (LIST.SET.sub-cons-congr θ) n)

   wkenM : ∀{Γ A C m} → MTerm Γ C m → MTerm (A :: Γ) C m
   wkenM = wkM LIST.SET.sub-wken

   exchM : ∀{Γ A B C m} → MTerm (A :: B :: Γ) C m → MTerm (B :: A :: Γ) C m
   exchM = wkM LIST.SET.sub-exch

   cntrM : ∀{Γ A C m} → MTerm (A :: A :: Γ) C m → MTerm (A :: Γ) C m
   cntrM = wkM LIST.SET.sub-cntr 

   -- Weakening outside the metric
   wk : ∀{Γ Δ A} → Γ ⊆ Δ → Term Γ A → Term Δ A 
   wk θ n = tm→ (wkM θ (snd (→tm n)))

   {- We don't actually end up using this version 
   wk : ∀{Γ Δ A} → Γ ⊆ Δ → Term Γ A → Term Δ A 
   wk θ (var n) = var (θ n)
   wk θ (n1 · n2) = wk θ n1 · wk θ n2
   wk θ (Λ n) = Λ (wk (LIST.SET.sub-cons-congr θ) n) -}

   wken : ∀{Γ A C} → Term Γ C → Term (A :: Γ) C
   wken = wk LIST.SET.sub-wken

   exch : ∀{Γ A B C} → Term (A :: B :: Γ) C → Term (B :: A :: Γ) C
   exch = wk LIST.SET.sub-exch

   cntr : ∀{Γ A C} → Term (A :: A :: Γ) C → Term (A :: Γ) C 
   cntr = wk LIST.SET.sub-cntr 

   -- Substitution
   subst : ∀{Γ A C} → Term Γ A → Term (A :: Γ) C → Term Γ C
   subst n1 n2 = substM n1 (snd (→tm n2))
    where
      substM : ∀{Γ A C m} → Term Γ A → MTerm (A :: Γ) C m → Term Γ C
      substM n1 (var Z) = n1
      substM n1 (var (S n)) = var n
      substM n1 (n · n') = substM n1 n · substM n1 n'
      substM n1 (Λ n) = Λ (substM (wken n1) (exchM n))

   {- We don't actually end up using this version 
   subst : ∀{Γ A C} → Term Γ A → Term (A :: Γ) C → Term Γ C
   subst = tm-subst [] _
    where
      var-subst : ∀{A C} (Γ Γ' : Ctx)
         → Term Γ' A
         → C ∈ (Γ ++ [ A ] ++ Γ') 
         → Term (Γ ++ Γ') C
      var-subst [] Γ' n1 Z = n1
      var-subst [] Γ' n1 (S n) = var n
      var-subst (_ :: Γ) Γ' n1 Z = var Z
      var-subst (_ :: Γ) Γ' n1 (S n) = wken (var-subst Γ Γ' n1 n)
 
      tm-subst : ∀{A C} (Γ Γ' : Ctx) 
         → Term Γ' A
         → Term (Γ ++ [ A ] ++ Γ') C 
         → Term (Γ ++ Γ') C 
      tm-subst Γ Γ' n1 (var n) = var-subst Γ Γ' n1 n
      tm-subst Γ Γ' n1 (n · n') = tm-subst Γ Γ' n1 n · tm-subst Γ Γ' n1 n'
      tm-subst Γ Γ' n1 (Λ n) = Λ (tm-subst (_ :: Γ) Γ' n1 n) -}

   module TEST where
   
      combI : ∀{t} → Term [] (t ⊃ t)
      combI = Λ (var Z)

      combK : ∀{t s} → Term [] (t ⊃ s ⊃ t)
      combK = Λ (Λ (var (S Z)))

      combS : ∀{t s r} → Term [] ((r ⊃ s ⊃ t) ⊃ (r ⊃ s) ⊃ r ⊃ t)
      combS = Λ (Λ (Λ (var (S (S Z)) · var Z · (var (S Z) · var Z))))

   -- Simultaneous substitutions, inspired by a note by commenter "thecod" 
   -- on the aforementioned blog post.
   module SIMULTANEOUS where

      -- Substitutions give a list 
      Subst : Ctx → Ctx → Set
      Subst Γ Δ = LIST.All (Term Δ) Γ

      subst-all : ∀{Γ Δ A} → Subst Γ Δ → Term Γ A → Term Δ A
      subst-all θ (var n) = LIST.ALL.pull n θ
      subst-all θ (n · n') = subst-all θ n · subst-all θ n'
      subst-all θ (Λ n) = 
         Λ (subst-all (LIST.ALL.cons (var Z) (LIST.ALL.map wken θ)) n)