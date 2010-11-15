{- The canonical forms of the simply typed lambda calculus -}
-- Foiled by Agda's termination checker, which does not understand the
-- reduces-style argument. (For an example of how Twelf handles this with 
-- a %reduce declaration, see 
-- http://twelf.plparty.org/wiki/Verifications_and_uses) 

{-# OPTIONS --no-termination-check #-}

module Demo.CanonicalForms where

open import Prelude

infixr 5 _⊃_
data Type : Set where
   con : String → Type
   _⊃_ : Type → Type → Type

Ctx = List Type

_⊆_ = LIST.SET.Sub

module TERMS (sig : String → Maybe Type) where
   mutual 
      infixl 5 _·_
      data Neut (Γ : Ctx) : Type → Set where
         var : ∀{A} → A ∈ Γ → Neut Γ A
         con : (c : String) {ch : Check (isSome (sig c))}
            → Neut Γ (valOf (sig c) {ch})
         _·_ : ∀{A B} 
            → Neut Γ (A ⊃ B)
            → Norm Γ A
            → Neut Γ B         

      data Norm (Γ : Ctx) : Type → Set where
         ⟨_⟩ : ∀{Q}
            → Neut Γ (con Q)
            → Norm Γ (con Q)
         Λ : ∀{A B}
            → Norm (A :: Γ) B 
            → Norm Γ (A ⊃ B)

   data Metric : Set where
      ○ : Metric
      _●_ : Metric → Metric → Metric
      > : Metric → Metric

   mutual
      data mNeut (Γ : Ctx) : Metric → Type → Set where
         var : ∀{A} → A ∈ Γ 
            → mNeut Γ ○ A
         con : (c : String) {ch : Check (isSome (sig c))}
            → mNeut Γ ○ (valOf (sig c) {ch})
         _·_ : ∀{A B mA mB} 
            → mNeut Γ mA (A ⊃ B)
            → mNorm Γ mB A
            → mNeut Γ (mA ● mB) B         

      data mNorm (Γ : Ctx) : Metric → Type → Set where
         ⟨_⟩ : ∀{Q m}
            → mNeut Γ m (con Q)
            → mNorm Γ (> m) (con Q)
         Λ : ∀{A B m}
            → mNorm (A :: Γ) m B 
            → mNorm Γ (> m) (A ⊃ B)

   mutual
      neut→ : ∀{Γ A} → Neut Γ A → ∃ λ N → mNeut Γ N A
      neut→ (var n) = , var n
      neut→ (con c) = , con c
      neut→ (r · n) = , snd (neut→ r) · snd (norm→ n)

      norm→ : ∀{Γ A} → Norm Γ A → ∃ λ N → mNorm Γ N A
      norm→ ⟨ r ⟩ = , ⟨ snd (neut→ r) ⟩
      norm→ (Λ n) = , Λ (snd (norm→ n))

   mutual
      →neut : ∀{Γ N A} → mNeut Γ N A → Neut Γ A
      →neut (var n) = var n
      →neut (con c) = con c
      →neut (r · n) = →neut r · →norm n

      →norm : ∀{Γ N A} → mNorm Γ N A → Norm Γ A
      →norm ⟨ r ⟩ = ⟨ →neut r ⟩
      →norm (Λ n) = Λ (→norm n)

   mutual
      wkenR : ∀{Γ Δ A} → Γ ⊆ Δ → Neut Γ A → Neut Δ A
      wkenR θ (var n) = var (θ n)
      wkenR θ (con c) = con c
      wkenR θ (r · n) = wkenR θ r · wkenN θ n

      wkenN : ∀{Γ Δ A} → Γ ⊆ Δ → Norm Γ A → Norm Δ A
      wkenN θ ⟨ r ⟩ = ⟨ wkenR θ r ⟩
      wkenN θ (Λ n) = Λ (wkenN (LIST.SET.sub-cons-congr θ) n)

   mutual
      wkenmNeut : ∀{Γ Δ N A} → Γ ⊆ Δ → mNeut Γ N A → mNeut Δ N A
      wkenmNeut θ (var n) = var (θ n)
      wkenmNeut θ (con c) = con c
      wkenmNeut θ (r · n) = wkenmNeut θ r · wkenmNorm θ n

      wkenmNorm : ∀{Γ Δ N A} → Γ ⊆ Δ → mNorm Γ N A → mNorm Δ N A
      wkenmNorm θ ⟨ r ⟩ = ⟨ wkenmNeut θ r ⟩
      wkenmNorm θ (Λ n) = Λ (wkenmNorm (LIST.SET.sub-cons-congr θ) n)
   
   wken : ∀{Γ A C} → Norm Γ C → Norm (A :: Γ) C  
   wken = wkenN LIST.SET.sub-wken

   exchm : ∀{Γ A B C N} → mNorm (A :: B :: Γ) N C → mNorm (B :: A :: Γ) N C  
   exchm = wkenmNorm LIST.SET.sub-exch

   head : ∀{Γ N A C} → mNeut (A :: Γ) N C → Bool
   head (var Z) = True
   head (var (S n)) = False 
   head (con c) = False
   head (r · _) = head r

   mutual 
      substNN : ∀{Γ A N C} 
         → Norm Γ A 
         → mNorm (A :: Γ) N C 
         → Norm Γ C
      substNN n1 ⟨ r ⟩ with BOOL.options (head r)
      ... | Inl eq = substRN n1 r eq
      ... | Inr eq = ⟨ substRR n1 r eq ⟩
      substNN n1 (Λ n2) = Λ (substNN (wken n1) (exchm n2))

      substRR : ∀{Γ A N C} 
         → Norm Γ A 
         → (r : mNeut (A :: Γ) N C)
         → head r ≡ False
         → Neut Γ C
      substRR n1 (var Z) ()
      substRR n1 (var (S n)) eq = var n
      substRR n1 (con c) eq = con c
      substRR n1 (r · n) eq = substRR n1 r eq · substNN n1 n

      substRN : ∀{Γ A N C} 
         → Norm Γ A 
         → (r : mNeut (A :: Γ) N C)
         → head r ≡ True
         → Norm Γ C
      substRN n1 (var Z) _ = n1
      substRN n1 (var (S n)) ()
      substRN n1 (con c) ()
      substRN n1 (r · n) eq with substRN n1 r eq
      ... | Λ n' = substNN (substNN n1 n) (snd (norm→ n'))

module TEST where
   sig : String → Maybe Type
   sig "lam" = Inl ((con "exp" ⊃ con "exp") ⊃ con "exp")
   sig "app" = Inl (con "exp" ⊃ con "exp" ⊃ con "exp")
   sig _ = Inr <>

   open TERMS sig public
   
   combI : Norm [] (con "exp")
   combI = ⟨ con "lam" · Λ ⟨ var Z ⟩ ⟩

   combK : Norm [] (con "exp")
   combK = ⟨ con "lam" · Λ ⟨ con "lam" · Λ ⟨ var (S Z) ⟩ ⟩ ⟩

   combS : Norm [] (con "exp")
   combS = 
      ⟨ con "lam" · Λ ⟨ con "lam" · Λ ⟨ con "lam" · Λ 
       ⟨ con "app" · 
        ⟨ con "app" · ⟨ var (S (S Z)) ⟩ · ⟨ var Z ⟩ ⟩ · 
        ⟨ con "app" · ⟨ var (S Z) ⟩ · ⟨ var Z ⟩ ⟩ ⟩ ⟩ ⟩ ⟩