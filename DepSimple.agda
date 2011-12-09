open import Prelude hiding (⊤ ; abort)

module DepSimple where

data Pol : Set where
  ⁻ : Pol
  ⁺ : Pol  
 
data Type : Pol → Set where
  c : {⁼ : Pol} → Type ⁼
  ↓ : (A⁻ : Type ⁻) → Type ⁺
  false : Type ⁺ 
  _⊕_ : (A⁺ B⁺ : Type ⁺) → Type ⁺ 
  true : Type ⁺
  _⊗_ : (A⁺ B⁺ : Type ⁺) → Type ⁺
  ↑ : (A⁺ : Type ⁺) → Type ⁻
  _⊸_ : (A⁺ : Type ⁺) (B⁻ : Type ⁻) → Type ⁻
  ⊤ : Type ⁻
  _&_ : (A⁻ B⁻ : Type ⁻) → Type ⁻

data Stable : Type ⁻ → Set where
  c : Stable c
  ↑ : ∀{A⁺} → Stable (↑ A⁺)

Ctx = List (Maybe (Type ⁻))
ICtx = List (Type ⁺)

_⊆_ : Ctx → Ctx → Set
_⊆_ = LIST.SET.Sub

mutual
  data Value (γ : Ctx) : Type ⁺ → Set where
    ⁺ : (x : Nothing ∈ γ) → Value γ c
    ⟨_⟩⁻ : ∀{a⁻} (N : Term γ [] a⁻) → Value γ (↓ a⁻)    
    inl : ∀{a⁺ b⁺} (V : Value γ a⁺) → Value γ (a⁺ ⊕ b⁺)
    inr : ∀{a⁺ b⁺} (V : Value γ b⁺) → Value γ (a⁺ ⊕ b⁺)
    ⟪⟫⁺ : Value γ true
    ⟪_,_⟫⁺ : ∀{a⁺ b⁺} (V₁ : Value γ a⁺) (V₂ : Value γ b⁺) → Value γ (a⁺ ⊗ b⁺)

  data Term (γ : Ctx) : ICtx → Type ⁻ → Set where
    foc : ∀{a⁻ c⁻}
      (x : Just a⁻ ∈ γ)
      (atm : Stable c⁻)
      (S : Spine γ a⁻ c⁻)
      → Term γ [] c⁻
    ·⁺ : ∀{ω c⁻} 
      (N : Term (Nothing :: γ) ω c⁻)
      → Term γ (c :: ω) c⁻ 
    ·⁻ : ∀{ω a⁻ c⁻} 
      (N : Term (Just a⁻ :: γ) ω c⁻)
      → Term γ (↓ a⁻ :: ω) c⁻ 
    abort : ∀{ω c⁻} 
      → Term γ (false :: ω) c⁻
    ⟦_,_⟧ : ∀{ω a⁺ b⁺ c⁻} 
      (N₁ : Term γ (a⁺ :: ω) c⁻)
      (N₂ : Term γ (b⁺ :: ω) c⁻)
      → Term γ (a⁺ ⊕ b⁺ :: ω) c⁻
    ⟪⟫· : ∀{ω c⁻}
      (N₁ : Term γ ω c⁻)
      → Term γ (true :: ω) c⁻
    ⟨_⟩⁺ : ∀{a⁺}
      (V : Value γ a⁺)
      → Term γ [] (↑ a⁺)
    Λ : ∀{a⁺ b⁻}
      (N : Term γ [ a⁺ ] b⁻)
      → Term γ [] (a⁺ ⊸ b⁻)
    ⟪⟫⁻ : Term γ [] ⊤
    ⟪_,_⟫⁻ : ∀{a⁻ b⁻}
      (N₁ : Term γ [] a⁻)
      (N₂ : Term γ [] b⁻)
      → Term γ [] (a⁻ & b⁻)
  
  data Spine (γ : Ctx) : Type ⁻ → Type ⁻ → Set where
     
{-

 
  data Term (γ : Ctx) : Type ⁻ → Type ⁺ → Set where
    foc : ∀{a⁻ ω}
      (x : Inl a⁻ ∈ γ)
      (atm : Stable γ)
      (Sp : Term γ ω a⁻)
      → 

    ↑R : ∀{A⁺}
      (σ : Γ ⊢[ [ A⁺ ] ])
      → Γ ⊢ ↑ A⁺ 
    ⊤R : Γ ⊢ ⊤ 
    &R : ∀{A⁻ B⁻}
      (N₁ : Γ ⊢ A⁻)
      (N₂ : Γ ⊢ B⁻)
      → Γ ⊢ A⁻ & B⁻
    ⊸R : ∀{A⁺ B⁻}
      (N : Γ ∣ [ A⁺ ] ⊢ B⁻)
      → Γ ⊢ A⁺ ⊸ B⁻
  
  data _[_]⊢_ (Γ : Ctx) : Type ⁻ → Type ⁻ → Set where
    nil : ∀{Q}
      → Γ [ c Q ]⊢ c Q
    cont : ∀{A⁺ C⁻}
      (N : Γ ∣ [ A⁺ ] ⊢ C⁻)
      → Γ [ ↑ A⁺ ]⊢ C⁻
    &L₁ : ∀{A⁻ B⁻ C⁻}
      (Sp : Γ [ A⁻ ]⊢ C⁻)
      → Γ [ A⁻ & B⁻ ]⊢ C⁻
    &L₂ : ∀{A⁻ B⁻ C⁻}
      (Sp : Γ [ B⁻ ]⊢ C⁻)
      → Γ [ A⁻ & B⁻ ]⊢ C⁻
    ⊸L : ∀{A⁺ B⁻ C⁻}
      (σ : Γ ⊢[ [ A⁺ ] ])
      (Sp : Γ [ B⁻ ]⊢ C⁻)
      → Γ [ A⁺ ⊸ B⁻ ]⊢ C⁻ 

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
    falseL : ∀{Δ C⁻}
      → Γ ∣ false :: Δ ⊢ C⁻
    ⊕L : ∀{A⁺ B⁺ Δ C⁻}
      (N₁ : Γ ∣ A⁺ :: Δ ⊢ C⁻)
      (N₂ : Γ ∣ B⁺ :: Δ ⊢ C⁻)
      → Γ ∣ A⁺ ⊕ B⁺ :: Δ ⊢ C⁻
    trueL : ∀{Δ C⁻}
      (N : Γ ∣ Δ ⊢ C⁻)
      → Γ ∣ true :: Δ ⊢ C⁻
    ⊗L : ∀{A⁺ B⁺ Δ C⁻}
      (N : Γ ∣ A⁺ :: B⁺ :: Δ ⊢ C⁻)
      → Γ ∣ A⁺ ⊗ B⁺ :: Δ ⊢ C⁻

mutual
  wkN : ∀{Γ Γ' A⁻} → Γ ⊆ Γ' → Γ ⊢ A⁻ → Γ' ⊢ A⁻ 
  wkN θ N = {!N!} 

  wkNI : ∀{Γ Γ' Δ A⁻} → Γ ⊆ Γ' → Γ ∣ Δ ⊢ A⁻ → Γ' ∣ Δ ⊢ A⁻ 
  wkNI θ N = {!!} 

  wkSp : ∀{Γ Γ' C⁻ A⁻} → Γ ⊆ Γ' → Γ [ A⁻ ]⊢ C⁻ → Γ' [ A⁻ ]⊢ C⁻
  wkSp θ σ = {!!} 

  wkσ : ∀{Γ Γ' Δ} → Γ ⊆ Γ' → Γ ⊢[ Δ ] → Γ' ⊢[ Δ ] 
  wkσ θ σ = {!!} 


-- Termination metric on terms
mutual 
  data mA⁻ : Type ⁻ → Set where
    c : ∀{Q} → mA⁻ (c Q)
    ↑ : ∀{A⁺} (m : mA⁺ A⁺) → mA⁻ (↑ A⁺)
    ⊤ : mA⁻ ⊤
    & : ∀{A⁻ B⁻} (m₁ : mA⁻ A⁻) (m₂ : mA⁻ B⁻) → mA⁻ (A⁻ & B⁻) 
    ⊸ : ∀{A⁺ B⁻} (m₁ : mA⁺ A⁺) (m₂ : mA⁻ B⁻) → mA⁻ (A⁺ ⊸ B⁻)

  data mA⁺ : Type ⁺ → Set where
    Δ : ∀{A⁺} (m : mΔ [ A⁺ ]) → mA⁺ A⁺

  data mΔ : List (Type ⁺) → Set where
    nil : mΔ []
    c : ∀{Q Δ} (m : mΔ Δ) → mΔ (c Q :: Δ)
    ↓ : ∀{A⁻ Δ} (m₁ : mA⁻ A⁻) (m₂ : mΔ Δ) → mΔ (↓ A⁻ :: Δ)
    ⊗ : ∀{A⁺ B⁺ Δ} (m : mΔ (A⁺ :: B⁺ :: Δ)) → mΔ (A⁺ ⊗ B⁺ :: Δ)
    ⊕ : ∀{A⁺ B⁺ Δ} (m₁ : mΔ (A⁺ :: Δ)) (m₂ : mΔ (B⁺ :: Δ)) → mΔ (A⁺ ⊕ B⁺ :: Δ)
    true : ∀{Δ} (m : mΔ Δ) → mΔ (true :: Δ) 
    false : ∀{Δ} → mΔ (false :: Δ)


-- Selects whether a variable in the context is critical or not
Γ? : ∀{α α' Γ} (Γ' : Ctx) 
  → (α' ∈ Γ' ++ α :: Γ) 
  → (α ≡ α') + (α' ∈ Γ' ++ Γ)
Γ? [] Z = Inl refl
Γ? [] (S x) = Inr x
Γ? (_ :: Γ') Z = Inr Z
Γ? (_ :: Γ') (S x) with Γ? Γ' x
... | Inl Refl = Inl refl
... | Inr y = Inr (S y)


-- Cut admissibility
mutual
  -- Principal cuts 
  -- Negative connectives
  subst⁻ : ∀{A⁻ Γ γ}  (Γ' : Ctx)
    → mA⁻ A⁻
    → Stable γ
    → Γ ⊢ A⁻
    → (Γ' ++ Γ) [ A⁻ ]⊢ γ
    → (Γ' ++ Γ) ⊢ γ
  subst⁻ Γ' c a (foc x atm Sp) nil = 
    wkN (LIST.SET.sub-appendl _ Γ') (foc x atm Sp)
  subst⁻ Γ' (↑ m) a (foc x atm Sp) (cont N) = 
    foc (LIST.SET.sub-appendl _ Γ' x) {!!}
      (left⁻ [] m a (wkSp (LIST.SET.sub-appendl _ Γ') Sp) N)
  subst⁻ Γ' (↑ (Δ m)) a (↑R σ) (cont N) = subst⁺ Γ' m σ N
  subst⁻ Γ' ⊤ a M ()
  subst⁻ Γ' (& m₁ m₂) a (foc x () Sp) M
  subst⁻ Γ' (& m₁ m₂) a (&R N₁ N₂) (&L₁ Sp) = subst⁻ Γ' m₁ a N₁ Sp
  subst⁻ Γ' (& m₁ m₂) a (&R N₁ N₂) (&L₂ Sp) = subst⁻ Γ' m₂ a N₂ Sp
  subst⁻ Γ' (⊸ m₁ m₂) a (foc x () Sp) Sp'
  subst⁻ Γ' (⊸ (Δ m₁) m₂) a (⊸R N) (⊸L σ Sp) = 
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
  subst⁺ Γ' (true m) (trueR σ) (trueL N) = subst⁺ Γ' m σ N
  subst⁺ Γ' (⊗ m) (⊗R σ) (⊗L N) = subst⁺ Γ' m σ N


  -- Right commutive cases ("Rightist substitution")
  -- Negative connectives, right rules
  cutN : ∀{Γ A⁻ C⁻} (Γ' : Ctx)
    → mA⁻ A⁻
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

  -- Positive connectives, left rules
  cutNI : ∀{Γ A⁻ Δ C⁻} (Γ' : Ctx)
    → mA⁻ A⁻
    → Γ ⊢ A⁻
    → (Γ' ++ Inl A⁻ :: Γ) ∣ Δ ⊢ C⁻
    → (Γ' ++ Γ) ∣ Δ ⊢ C⁻
  cutNI Γ' m M (nil N) = nil (cutN Γ' m M N)
  cutNI Γ' m M (cL N) = cL (cutNI (_ :: Γ') m M N)
  cutNI Γ' m M (↓L N) = ↓L (cutNI (_ :: Γ') m M N)
  cutNI Γ' m M falseL = falseL
  cutNI Γ' m M (⊕L N₁ N₂) = ⊕L (cutNI Γ' m M N₁) (cutNI Γ' m M N₂)
  cutNI Γ' m M (trueL N) = trueL (cutNI Γ' m M N)
  cutNI Γ' m M (⊗L N) = ⊗L (cutNI Γ' m M N) 

  -- Positive connectives, right rules
  cutσ : ∀{Γ A⁻ Δ} (Γ' : Ctx)
    → mA⁻ A⁻
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

  -- Negative connectives, left rules
  cutSp : ∀{Γ A⁻ B⁻ C⁻} (Γ' : Ctx)
    → mA⁻ A⁻
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
  left⁻ : ∀{Γ B⁻ A⁺ γ} (Γ' : Ctx)
    → mA⁺ A⁺
    → Stable γ
    → Γ' ++ Γ [ B⁻ ]⊢ ↑ A⁺
    → Γ ∣ [ A⁺ ] ⊢ γ
    → Γ' ++ Γ [ B⁻ ]⊢ γ
  left⁻ Γ' m a (cont M) N = cont (left⁺ Γ' m a M N)
  left⁻ Γ' m a (&L₁ Sp) N = &L₁ (left⁻ Γ' m a Sp N)
  left⁻ Γ' m a (&L₂ Sp) N = &L₂ (left⁻ Γ' m a Sp N)
  left⁻ Γ' m a (⊸L σ Sp) N = ⊸L σ (left⁻ Γ' m a Sp N)

  -- Positive connectives
  left⁺ : ∀{Γ A⁺ Δ γ} (Γ' : Ctx)
    → mA⁺ A⁺
    → Stable γ
    → Γ' ++ Γ ∣ Δ ⊢ ↑ A⁺
    → Γ ∣ [ A⁺ ] ⊢ γ
    → Γ' ++ Γ ∣ Δ ⊢ γ
  left⁺ Γ' m a (nil (foc x atm Sp)) N = 
    nil (foc x a (left⁻ Γ' m a Sp N))
  left⁺ Γ' (Δ m) a (nil (↑R σ)) N = 
    nil (subst⁺ [] m σ (wkNI (LIST.SET.sub-appendl _ Γ') N))
  left⁺ Γ' m a (cL M) N = cL (left⁺ (_ :: Γ') m a M N)
  left⁺ Γ' m a (↓L M) N = ↓L (left⁺ (_ :: Γ') m a M N)
  left⁺ Γ' m a falseL N = falseL
  left⁺ Γ' m a (⊕L N₁ N₂) N = ⊕L (left⁺ Γ' m a N₁ N) (left⁺ Γ' m a N₂ N)
  left⁺ Γ' m a (trueL M) N = trueL (left⁺ Γ' m a M N)
  left⁺ Γ' m a (⊗L M) N = ⊗L (left⁺ Γ' m a M N)



-}