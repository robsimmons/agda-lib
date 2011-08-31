-- Canonical adjoint logic

{-# OPTIONS --no-termination-check #-}

module CanonicalAdjointLogic where

open import Prelude

data Pol : Set where
  ⁺ : Pol
  ⁻ : Pol

_⊆_ : ∀{A} → List A → List A → Set
xs ⊆ ys = LIST.SET.Sub xs ys

module TYPES (Atom : Set) where

  infixr 5 _⇒_
  infixr 5 _⊃_

  mutual 
    data VType : Pol → Set where
      con⁺ : (Q : Atom) → VType ⁺
      con⁻ : (Q : Atom) → VType ⁻
      U : (A : TType ⁻) → VType ⁻
      _⇒_ : (A : VType ⁺) (B : VType ⁻) → VType ⁻
      ↓ : (A : TType ⁻) → VType ⁺
      ↑ : (A : VType ⁺) → VType ⁻

    data TType : Pol → Set where
      con⁺ : (Q : Atom) → TType ⁺
      con⁻ : (Q : Atom) → TType ⁻
      F : (A : TType ⁺) → TType ⁺
      _⊃_ : (A : TType ⁺) (B : TType ⁻) → TType ⁻
      ↓ : (A : TType ⁻) → TType ⁺
      ↑ : (A : TType ⁺) → TType ⁻
  
module TERMS (Atom : Set ; Const : Set ; sig : Const → TYPES.VType Atom ⁻) where

  open TYPES Atom
  VCtx = List (VType ⁻)
  TCtx = List (TType ⁻)

{-
  mutual
    infixl 5 _·_

    data Neut (Δ : VCtx) (Γ : Ctx) : VType ⁻ → Set where
      var : ∀{A} → A ∈ Γ → Neut Δ Γ A
      con : ∀{A} (c : Const) 
        (eq : sig c ≡ A)
        → Neut Δ Γ A
      _·_ : ∀{A B}
        (R : Neut Δ Γ (⟨ A ⟩ ⊃ B))
        (N : Norm Δ Γ A)
        → Neut Δ Γ B
      _·'_ : ∀{A B} 
        (R : Neut Δ Γ (U A ⊃ B))
        (x : A ∈ Δ)
        → Neut Δ Γ B

    data Norm (Δ : VCtx) (Γ : Ctx) : VType ⁻ → Set where
      ⟨_⟩ : ∀{Q}
        (R : Neut Δ Γ (con Q))
        → Norm Δ Γ (con Q)
      Λ_ : ∀{A B}
        (N : Norm Δ (A :: Γ) B)
        → Norm Δ Γ (⟨ A ⟩ ⊃ B)
      
  wk : ∀{Γ Γ' Δ Δ' A} → Δ ⊆ Δ' → Γ ⊆ Γ' → Norm Δ Γ A → Norm Δ' Γ' A
  wk = wkN
   where
   mutual
    wkR : ∀{Γ Γ' Δ Δ' A} → Δ ⊆ Δ' → Γ ⊆ Γ' → Neut Δ Γ A → Neut Δ' Γ' A
    wkR θΔ θΓ (var y) = var (θΓ y)
    wkR θΔ θΓ (con c Refl) = con c refl
    wkR θΔ θΓ (R · N) = wkR θΔ θΓ R · wkN θΔ θΓ N
    wkR θΔ θΓ (R ·' x) = wkR θΔ θΓ R ·' θΔ x

    wkN : ∀{Γ Γ' Δ Δ' A} → Δ ⊆ Δ' → Γ ⊆ Γ' → Norm Δ Γ A → Norm Δ' Γ' A
    wkN θΔ θΓ ⟨ R ⟩ = ⟨ wkR θΔ θΓ R ⟩
    wkN θΔ θΓ (Λ N) = Λ wkN θΔ (LIST.SET.sub-cons-congr θΓ) N
  

  -- Is this the variable we are looking for (the critical variable)?
  crit : ∀{A B Γ} (Γ' : Ctx) → A ∈ (Γ' ++ B :: Γ) → Bool
  crit [] Z = True
  crit [] (S n) = False
  crit (_ :: Γ') Z = False
  crit (_ :: Γ') (S n) = crit Γ' n
 
  -- Is the head a critical variable?
  head : ∀{Δ Γ A C} (Γ' : Ctx) → Neut Δ (Γ' ++ A :: Γ) C → Bool
  head Γ' (var y) = crit Γ' y
  head Γ' (con c Refl) = False
  head Γ' (R · N) = head Γ' R
  head Γ' (R ·' x) = head Γ' R

  -- Is the head a valid variable?
  vhead : ∀{Δ Γ C} → Neut Δ Γ C → Bool
  vhead (var y) = False
  vhead (con c Refl) = False
  vhead (R · N) = vhead R
  vhead (R ·' x) = vhead R


  -- Weaken a non-critical variable appropriately
  fixup : ∀{A B Γ} (Γ' : Ctx) (x : A ∈ (Γ' ++ B :: Γ))
    → crit Γ' x ≡ False 
    → A ∈ Γ' ++ Γ
  fixup [] Z ()
  fixup [] (S n) eq = n
  fixup (_ :: Γ') Z eq = Z
  fixup (_ :: Γ') (S n) eq = S (fixup Γ' n eq)

  equal : ∀{A B Γ} (Γ' : Ctx) (x : A ∈ (Γ' ++ B :: Γ))
    → crit Γ' x ≡ True 
    → A ≡ B
  equal [] Z eq = refl
  equal [] (S n) ()
  equal (x :: Γ') Z ()
  equal (_ :: Γ') (S n) eq = equal Γ' n eq

  mutual
    subst : ∀{Δ Γ A C} (Δ' : VCtx) (Γ' : Ctx) 
      → Norm Δ Γ A 
      → Norm (Δ' ++ Δ) (Γ' ++ A :: Γ) C 
      → Norm (Δ' ++ Δ) (Γ' ++ Γ) C
    subst Δ' Γ' M ⟨ R ⟩ with BOOL.options (head Γ' R)
    ... | Inl eq = substN Δ' Γ' M R eq
    ... | Inr eq = ⟨ substR Δ' Γ' M R eq ⟩
    subst Δ' Γ' M (Λ N) = Λ subst Δ' (_ :: Γ') M N

    substR : ∀{Γ A C Δ} (Δ' : VCtx) (Γ' : Ctx)
      → Norm Δ Γ A
      → (R : Neut (Δ' ++ Δ) (Γ' ++ A :: Γ) C)
      → head Γ' R ≡ False
      → Neut (Δ' ++ Δ) (Γ' ++ Γ) C
    substR Δ' Γ' M (var y) eq = var (fixup Γ' y eq)
    substR Δ' Γ' M (con c Refl) eq = con c refl
    substR Δ' Γ' M (R · N) eq = substR Δ' Γ' M R eq · subst Δ' Γ' M N
    substR Δ' Γ' M (R ·' x) eq = substR Δ' Γ' M R eq ·' x

    substN : ∀{Δ Γ A C} (Δ' : VCtx) (Γ' : Ctx) 
      → Norm Δ Γ A 
      → (R : Neut (Δ' ++ Δ) (Γ' ++ A :: Γ) C)
      → head Γ' R ≡ True
      → Norm (Δ' ++ Δ) (Γ' ++ Γ) C
    substN Δ' Γ' M (var y) eq with equal Γ' y eq
    ... | Refl = wk (LIST.SET.sub-appendl _ Δ') (LIST.SET.sub-appendl _ Γ') M
    substN Δ' Γ' M (con c Refl) ()
    substN Δ' Γ' M (R · N) eq with substN Δ' Γ' M R eq
    ... | Λ N' = subst [] [] (subst Δ' Γ' M N) N' 
    substN Δ' Γ' M (R ·' x) eq with substN Δ' Γ' M R eq 
    ... | () 

module TEST where
   data Atom : Set where
     exp : Atom
     nat : Atom
     bool : Atom

   data Const : Set where
     true : Const
     false : Const
     z : Const
     s : Const
     lam : Const
     app : Const

   open TYPES Atom

   sig : Const → VType ⁻
   sig true =  con bool
   sig false = con bool
   sig z =     con nat
   sig s =     ⟨ con nat ⟩ ⊃ con nat
   sig lam =   ⟨ ⟨ con exp ⟩ ⊃ con exp ⟩ ⊃ con exp
   sig app =   ⟨ con exp ⟩ ⊃ ⟨ con exp ⟩ ⊃ con exp

   open TERMS Atom Const sig public

   -- Example booleans
   tt : Norm [] [] (con bool)
   tt = ⟨ con true refl ⟩

   ff : Norm [] [] (con bool)
   ff = ⟨ con false refl ⟩
   
   -- Example natural numbers
   three : Norm [] [] (con nat)
   three = ⟨ con s refl · ⟨ con s refl · ⟨ con s refl · ⟨ con z refl ⟩ ⟩ ⟩ ⟩
 
   abortsig : ∀{A B C D} {E : Set} → Neut [] [] (A ⊃ B ⊃ C ⊃ D) → E
   abortsig (var ()) 
   abortsig (R ·' ())
   abortsig (con true ())
   abortsig (con false ())
   abortsig (con z ())
   abortsig (con s ()) 
   abortsig (con lam ())
   abortsig (con app ())
   abortsig (R · N) = abortsig R


   encodeN : Nat → Norm [] [] (con nat)
   encodeN Z = ⟨ con z refl ⟩
   encodeN (S n) = ⟨ con s refl · encodeN n ⟩

   decodeN : Norm [] [] (con nat) → Nat
   decodeN ⟨ var () ⟩ 
   decodeN ⟨ R ·' () ⟩
   decodeN ⟨ con true () ⟩ 
   decodeN ⟨ con false () ⟩
   decodeN ⟨ con z Refl ⟩ = Z
   decodeN ⟨ con s () ⟩
   decodeN ⟨ con lam () ⟩
   decodeN ⟨ con app () ⟩
   decodeN ⟨ var () · N ⟩
   decodeN ⟨ R ·' () · N' ⟩
   decodeN ⟨ con true () · N ⟩ 
   decodeN ⟨ con false () · N ⟩
   decodeN ⟨ con z () · N ⟩
   decodeN ⟨ con s Refl · N ⟩ = S (decodeN N)
   decodeN ⟨ con lam () · N ⟩
   decodeN ⟨ con app () · N ⟩
   decodeN ⟨ var () · N · N' ⟩ 
   decodeN ⟨ R ·' () · N · N' ⟩
   decodeN ⟨ con true () · N · N' ⟩ 
   decodeN ⟨ con false () · N · N' ⟩
   decodeN ⟨ con z () · N · N' ⟩
   decodeN ⟨ con s () · N · N' ⟩
   decodeN ⟨ con lam () · N · N' ⟩
   decodeN ⟨ con app () · N · N' ⟩
   decodeN ⟨ R · N · N' · N'' ⟩ = abortsig R

   inverses1 : (n : Nat) → n ≡ decodeN (encodeN n)
   inverses1 Z = refl
   inverses1 (S n) = NAT.s-cong (inverses1 n)

   inverses2 : (N : Norm [] [] (con nat)) → N ≡ encodeN (decodeN N)
   inverses2 ⟨ var () ⟩ 
   inverses2 ⟨ R ·' () ⟩
   inverses2 ⟨ con true () ⟩ 
   inverses2 ⟨ con false () ⟩
   inverses2 ⟨ con z Refl ⟩ = refl
   inverses2 ⟨ con s () ⟩
   inverses2 ⟨ con lam () ⟩
   inverses2 ⟨ con app () ⟩
   inverses2 ⟨ var () · N ⟩
   inverses2 ⟨ R ·' () · N' ⟩
   inverses2 ⟨ con true () · N ⟩ 
   inverses2 ⟨ con false () · N ⟩
   inverses2 ⟨ con z () · N ⟩
   inverses2 ⟨ con s Refl · N ⟩ = cong (inverses2 N)
    where
     cong : {N M : Norm [] [] (con nat)} 
       → N ≡ M
       → Id {_} {Norm [] [] (con nat)} ⟨ con s Refl · N ⟩ ⟨ con s Refl · M ⟩
     cong Refl = refl 
   inverses2 ⟨ con lam () · N ⟩
   inverses2 ⟨ con app () · N ⟩
   inverses2 ⟨ var () · N · N' ⟩ 
   inverses2 ⟨ R ·' () · N · N' ⟩
   inverses2 ⟨ con true () · N · N' ⟩ 
   inverses2 ⟨ con false () · N · N' ⟩
   inverses2 ⟨ con z () · N · N' ⟩
   inverses2 ⟨ con s () · N · N' ⟩
   inverses2 ⟨ con lam () · N · N' ⟩
   inverses2 ⟨ con app () · N · N' ⟩
   inverses2 ⟨ R · N · N' · N'' ⟩ = abortsig R

   -- Example expressions
   combI : Norm [] [] (con exp)
   combI = ⟨ con lam refl · Λ ⟨ var Z ⟩ ⟩

   combK : Norm [] [] (con exp)
   combK = ⟨ con lam refl · Λ ⟨ con lam refl · Λ ⟨ var (S Z) ⟩ ⟩ ⟩

   combS : Norm [] [] (con exp)
   combS = 
      ⟨ con lam refl · Λ ⟨ con lam refl · Λ ⟨ con lam refl · Λ 
       ⟨ con app refl · 
        ⟨ con app refl · ⟨ var (S (S Z)) ⟩ · ⟨ var Z ⟩ ⟩ · 
        ⟨ con app refl · ⟨ var (S Z) ⟩ · ⟨ var Z ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
   
   
{-
-}

{-
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


-}
-}