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
  data mA : Type ⁻ → Set where
    c : ∀{Q} → mA (c Q)
    ↑ : ∀{Δ} (m : mX Δ) → mA (↑ Δ)
    ⊤ : mA ⊤
    & : ∀{A⁻ B⁻} (m₁ : mA A⁻) (m₂ : mA B⁻) → mA (A⁻ & B⁻) 
    ⊸ : ∀{Δ B⁻} (m₁ : mΔ Δ) (m₂ : mA B⁻) → mA (Δ ⊸ B⁻)

  data mX : List (Type ⁺) → Set where
    X : ∀{Δ} (m : mΔ Δ) → mX Δ

  data mΔ : List (Type ⁺) → Set where
    nil : mΔ []
    c : ∀{Q Δ} (m : mΔ Δ) → mΔ (c Q :: Δ)
    ↓ : ∀{A⁻ Δ} (m₁ : mA A⁻) (m₂ : mΔ Δ) → mΔ (↓ A⁻ :: Δ)
    ⊗ : ∀{A⁺ B⁺ Δ} (m : mΔ (A⁺ :: B⁺ :: Δ)) → mΔ (A⁺ ⊗ B⁺ :: Δ)
    ⊕ : ∀{A⁺ B⁺ Δ} (m₁ : mΔ (A⁺ :: Δ)) (m₂ : mΔ (B⁺ :: Δ)) → mΔ (A⁺ ⊕ B⁺ :: Δ)
    true : ∀{Δ} (m : mΔ Δ) → mΔ (true :: Δ) 
    false : ∀{Δ} → mΔ (false :: Δ)

Γ? : ∀{α α' Γ} (Γ' : Ctx) 
  → (α' ∈ Γ' ++ α :: Γ) 
  → (α ≡ α') + (α' ∈ Γ' ++ Γ)
Γ? [] Z = Inl refl
Γ? [] (S x) = Inr x
Γ? (_ :: Γ') Z = Inr Z
Γ? (_ :: Γ') (S x) with Γ? Γ' x
... | Inl Refl = Inl refl
... | Inr y = Inr (S y)

mutual
  -- Right commutive cases
  -- Negative connectives, right rules
  cutN : ∀{Γ A⁻ C⁻} (Γ' : Ctx)
    → (m : mA A⁻)
    → Γ ⊢ A⁻
    → (Γ' ++ Inl A⁻ :: Γ) ⊢ C⁻
    → (Γ' ++ Γ) ⊢ C⁻
  cutN Γ' m M (foc x atm Sp) with Γ? Γ' x
  ... | Inl Refl = subst⁻ Γ' m atm M (cutSp Γ' m M Sp) -- PRINCIPAL
  ... | Inr y = foc y atm (cutSp Γ' m M Sp)
  cutN Γ' m M (↑R σ) = ↑R (cutσ Γ' m M σ)
  cutN Γ' m M ⊤R = ⊤R
  cutN Γ' m M (&R N₁ N₂) = &R (cutN Γ' m M N₁) (cutN Γ' m M N₂)
  cutN Γ' m M (⊸R N) = ⊸R (cutNI Γ' m M N)

  -- Negative connectives, left rules
  cutNI : ∀{Γ A⁻ Δ C⁻} (Γ' : Ctx)
    → (m : mA A⁻)
    → Γ ⊢ A⁻
    → (Γ' ++ Inl A⁻ :: Γ) ∣ Δ ⊢ C⁻
    → (Γ' ++ Γ) ∣ Δ ⊢ C⁻
  cutNI Γ' m M (nil N) = nil (cutN Γ' m M N)
  cutNI Γ' m M (cL N) = cL (cutNI (_ :: Γ') m M N)
  cutNI Γ' m M (↓L N) = ↓L (cutNI (_ :: Γ') m M N)
  cutNI Γ' m M falseE = falseE
  cutNI Γ' m M (⊕L N₁ N₂) = ⊕L (cutNI Γ' m M N₁) (cutNI Γ' m M N₂)
  cutNI Γ' m M (trueE N) = trueE (cutNI Γ' m M N)
  cutNI Γ' m M (⊗L N) = ⊗L (cutNI Γ' m M N) 

  -- Positive connectives, right rules
  cutσ : ∀{Γ A⁻ Δ} (Γ' : Ctx)
    → (m : mA A⁻)
    → Γ ⊢ A⁻
    → (Γ' ++ Inl A⁻ :: Γ) ⊢[ Δ ]
    → (Γ' ++ Γ) ⊢[ Δ ]
  cutσ Γ' m M nil = nil
  cutσ Γ' m M (cR x σ) with Γ? Γ' x
  ... | Inl () 
  ... | Inr y = cR y (cutσ Γ' m M σ)
  cutσ Γ' m M (↓R N σ) = ↓R (cutN Γ' m M N) (cutσ Γ' m M σ)
  cutσ Γ' m M (⊕R₁ σ) = ⊕R₁ (cutσ Γ' m M σ)
  cutσ Γ' m M (⊕R₂ σ) = ⊕R₂ (cutσ Γ' m M σ)
  cutσ Γ' m M (trueR σ) = trueR (cutσ Γ' m M σ)
  cutσ Γ' m M (⊗R σ) = ⊗R (cutσ Γ' m M σ)

  -- Positive connectives, left rules
  cutSp : ∀{Γ A⁻ B⁻ C⁻} (Γ' : Ctx)
    → (m : mA A⁻)
    → Γ ⊢ A⁻
    → (Γ' ++ Inl A⁻ :: Γ) [ B⁻ ]⊢ C⁻
    → (Γ' ++ Γ) [ B⁻ ]⊢ C⁻
  cutSp Γ' m M nil = nil
  cutSp Γ' m M (cont N) = cont (cutNI Γ' m M N)
  cutSp Γ' m M (&L₁ Sp) = &L₁ (cutSp Γ' m M Sp)
  cutSp Γ' m M (&L₂ Sp) = &L₂ (cutSp Γ' m M Sp)
  cutSp Γ' m M (⊸L σ Sp) = ⊸L (cutσ Γ' m M σ) (cutSp Γ' m M Sp)


  -- Left commutative cases ("Leftist substitution")
  -- Negative connectives
  left⁻ : ∀{Γ B⁻ Δ C⁻} (Γ' : Ctx)
    → mX Δ
    → Atomic C⁻
    → Γ' ++ Γ [ B⁻ ]⊢ ↑ Δ
    → Γ ∣ Δ ⊢ C⁻
    → Γ' ++ Γ [ B⁻ ]⊢ C⁻
  left⁻ Γ' m a (cont M) N = cont (left⁺ Γ' m a M N)
  left⁻ Γ' m a (&L₁ Sp) N = &L₁ (left⁻ Γ' m a Sp N)
  left⁻ Γ' m a (&L₂ Sp) N = &L₂ (left⁻ Γ' m a Sp N)
  left⁻ Γ' m a (⊸L σ Sp) N = ⊸L σ (left⁻ Γ' m a Sp N)

  -- Positive connectives
  left⁺ : ∀{Γ Δ Δ' C⁻} (Γ' : Ctx)
    → mX Δ
    → Atomic C⁻
    → Γ' ++ Γ ∣ Δ' ⊢ ↑ Δ
    → Γ ∣ Δ ⊢ C⁻
    → Γ' ++ Γ ∣ Δ' ⊢ C⁻
  left⁺ Γ' m a (nil (foc x atm Sp)) N = 
    nil (foc x a (left⁻ Γ' m a Sp N))
  left⁺ Γ' (X m) a (nil (↑R σ)) N = 
    nil (subst⁺ [] m σ (wkNI (LIST.SET.sub-appendl _ Γ') N))
  left⁺ Γ' m a (cL M) N = cL (left⁺ (_ :: Γ') m a M N)
  left⁺ Γ' m a (↓L M) N = ↓L (left⁺ (_ :: Γ') m a M N)
  left⁺ Γ' m a falseE N = falseE
  left⁺ Γ' m a (⊕L N₁ N₂) N = ⊕L (left⁺ Γ' m a N₁ N) (left⁺ Γ' m a N₂ N)
  left⁺ Γ' m a (trueE M) N = trueE (left⁺ Γ' m a M N)
  left⁺ Γ' m a (⊗L M) N = ⊗L (left⁺ Γ' m a M N)


  -- Principal cuts ("Hereditary reduction")
  -- Negative connectives
  subst⁻ : ∀{A⁻ Γ C⁻}  (Γ' : Ctx)
    → mA A⁻
    → Atomic C⁻
    → Γ ⊢ A⁻
    → (Γ' ++ Γ) [ A⁻ ]⊢ C⁻
    → (Γ' ++ Γ) ⊢ C⁻
  subst⁻ Γ' c a (foc x atm Sp) nil = 
    wkN (LIST.SET.sub-appendl _ Γ') (foc x atm Sp)
  subst⁻ Γ' (↑ m) a (foc x atm Sp) (cont N) = 
    foc (LIST.SET.sub-appendl _ Γ' x) a
      (left⁻ [] m a (wkSp (LIST.SET.sub-appendl _ Γ') Sp) N)
  subst⁻ Γ' (↑ (X m)) a (↑R σ) (cont N) = subst⁺ Γ' m σ N
  subst⁻ Γ' ⊤ a M ()
  subst⁻ Γ' (& m₁ m₂) a (foc x () Sp) M
  subst⁻ Γ' (& m₁ m₂) a (&R N₁ N₂) (&L₁ Sp) = subst⁻ Γ' m₁ a N₁ Sp
  subst⁻ Γ' (& m₁ m₂) a (&R N₁ N₂) (&L₂ Sp) = subst⁻ Γ' m₂ a N₂ Sp
  subst⁻ Γ' (⊸ m₁ m₂) a (foc x () Sp) Sp'
  subst⁻ Γ' (⊸ m₁ m₂) a (⊸R N) (⊸L σ Sp) = 
    subst⁻ [] m₂ a (subst⁺ [] m₁ σ (wkNI (LIST.SET.sub-appendl _ Γ') N)) Sp
 
  -- Positive connectives
  subst⁺ : ∀{Γ Δ C⁻} (Γ' : Ctx)
    → mΔ Δ
    → Γ ⊢[ Δ ]
    → (Γ' ++ Γ) ∣ Δ ⊢ C⁻
    → (Γ' ++ Γ) ⊢ C⁻
  subst⁺ Γ' nil nil (nil N) = N
  subst⁺ Γ' (c m) (cR x σ) (cL N) = 
    subst⁺ Γ' m σ (wkNI (LIST.SET.sub-cntr (LIST.SET.sub-appendl _ Γ' x)) N)
  subst⁺ Γ' (↓ m₁ m₂) (↓R M σ) (↓L N) = 
    subst⁺ Γ' m₂ σ (cutNI [] m₁ (wkN (LIST.SET.sub-appendl _ Γ') M) N) 
  subst⁺ Γ' (⊕ m₁ m₂) (⊕R₁ σ) (⊕L N₁ N₂) = subst⁺ Γ' m₁ σ N₁
  subst⁺ Γ' (⊕ m₁ m₂) (⊕R₂ σ) (⊕L N₁ N₂) = subst⁺ Γ' m₂ σ N₂
  subst⁺ Γ' false () falseL 
  subst⁺ Γ' (true m) (trueR σ) (trueE N) = subst⁺ Γ' m σ N
  subst⁺ Γ' (⊗ m) (⊗R σ) (⊗L N) = subst⁺ Γ' m σ N

