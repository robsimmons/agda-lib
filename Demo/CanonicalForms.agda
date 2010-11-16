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

_⊆_ : Ctx → Ctx → Set
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
      data MNeut (Γ : Ctx) : Type → Metric → Set where
         var : ∀{A} → A ∈ Γ 
            → MNeut Γ A ○
         con : (c : String) {ch : Check (isSome (sig c))}
            → MNeut Γ (valOf (sig c) {ch}) ○
         _·_ : ∀{A B mA mB} 
            → MNeut Γ (A ⊃ B) mA
            → MNorm Γ A mB
            → MNeut Γ B (mA ● mB)     

      data MNorm (Γ : Ctx) : Type → Metric → Set where
         ⟨_⟩ : ∀{Q m}
            → MNeut Γ (con Q) m
            → MNorm Γ (con Q) (> m)
         Λ : ∀{A B m}
            → MNorm (A :: Γ) B m 
            → MNorm Γ (A ⊃ B) (> m) 

   mutual
      →R : ∀{Γ A} → Neut Γ A → ∃ λ m → MNeut Γ A m
      →R (var n) = , var n
      →R (con c) = , con c
      →R (r · n) = , snd (→R r) · snd (→N n)

      →N : ∀{Γ A} → Norm Γ A → ∃ λ m → MNorm Γ A m
      →N ⟨ r ⟩ = , ⟨ snd (→R r) ⟩
      →N (Λ n) = , Λ (snd (→N n))

   mutual
      R→ : ∀{Γ A m} → MNeut Γ A m → Neut Γ A
      R→ (var n) = var n
      R→ (con c) = con c
      R→ (r · n) = R→ r · N→ n

      N→ : ∀{Γ A m} → MNorm Γ A m → Norm Γ A
      N→ ⟨ r ⟩ = ⟨ R→ r ⟩
      N→ (Λ n) = Λ (N→ n)

   wkM : ∀{Γ Δ A m} → Γ ⊆ Δ → MNorm Γ A m → MNorm Δ A m
   wkM = wkN
    where
     mutual
      wkR : ∀{Γ Δ A m} → Γ ⊆ Δ → MNeut Γ A m → MNeut Δ A m
      wkR θ (var n) = var (θ n)
      wkR θ (con c) = con c
      wkR θ (r · n) = wkR θ r · wkN θ n

      wkN : ∀{Γ Δ A m} → Γ ⊆ Δ → MNorm Γ A m → MNorm Δ A m
      wkN θ ⟨ r ⟩ = ⟨ wkR θ r ⟩
      wkN θ (Λ n) = Λ (wkN (LIST.SET.sub-cons-congr θ) n)

   wk : ∀{Γ Δ A} → Γ ⊆ Δ → Norm Γ A → Norm Δ A
   wk θ n = N→ (wkM θ (snd (→N n)))

   wken : ∀{Γ A C} → Norm Γ C → Norm (A :: Γ) C  
   wken = wk LIST.SET.sub-wken

   exchM : ∀{Γ A B C N} → MNorm (A :: B :: Γ) N C → MNorm (B :: A :: Γ) N C  
   exchM = wkM LIST.SET.sub-exch

   head : ∀{Γ N A C} → MNeut (A :: Γ) N C → Bool
   head (var Z) = True
   head (var (S n)) = False 
   head (con c) = False
   head (r · _) = head r

   subst : ∀{Γ A C} → Norm Γ A → Norm (A :: Γ) C → Norm Γ C
   subst n1 n2 = substNN n1 (snd (→N n2))
    where
     mutual
      substNN : ∀{Γ A C m} 
         → Norm Γ A 
         → MNorm (A :: Γ) C m 
         → Norm Γ C
      substNN n1 ⟨ r ⟩ with BOOL.options (head r)
      ... | Inl eq = substRN n1 r eq
      ... | Inr eq = ⟨ substRR n1 r eq ⟩
      substNN n1 (Λ n2) = Λ (substNN (wken n1) (exchM n2))

      substRR : ∀{Γ A C m} 
         → Norm Γ A 
         → (r : MNeut (A :: Γ) C m)
         → head r ≡ False
         → Neut Γ C
      substRR n1 (var Z) ()
      substRR n1 (var (S n)) eq = var n
      substRR n1 (con c) eq = con c
      substRR n1 (r · n) eq = substRR n1 r eq · substNN n1 n

      substRN : ∀{Γ A C m} 
         → Norm Γ A 
         → (r : MNeut (A :: Γ) C m)
         → head r ≡ True
         → Norm Γ C
      substRN n1 (var Z) _ = n1
      substRN n1 (var (S n)) ()
      substRN n1 (con c) ()
      substRN n1 (r · n) eq with substRN n1 r eq
      ... | Λ n' = substNN (substNN n1 n) (snd (→N n'))


module TEST where
   sig : String → Maybe Type
   sig "lam" = Just ((con "exp" ⊃ con "exp") ⊃ con "exp")
   sig "app" = Just (con "exp" ⊃ con "exp" ⊃ con "exp")
   sig _ = Nothing

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
