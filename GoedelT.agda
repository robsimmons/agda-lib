module GoedelT where

open import Prelude

_⊆_ : ∀{A} → List A → List A → Set
xs ⊆ ys = LIST.SET.Sub xs ys

-- Gödel's T
module GÖDEL-T where 

  data TTp : Set where
    nat : TTp
    bool : TTp
    _⇒_ : (A B : TTp) → TTp

  data TExp (Γ : List TTp) : TTp → Set where
    var : ∀{A} (x : A ∈ Γ) → TExp Γ A
    Λ_ : ∀{A B} (e : TExp (A :: Γ) B) → TExp Γ (A ⇒ B)
    _·_ : ∀{A B} (e₁ : TExp Γ (A ⇒ B)) (e₂ : TExp Γ A) → TExp Γ B
    true : TExp Γ bool
    false : TExp Γ bool
    ite : ∀{C} 
      (e : TExp Γ bool)
      (et : TExp Γ C)
      (ef : TExp Γ C)
      → TExp Γ C
    z : TExp Γ nat
    s : (e : TExp Γ nat) → TExp Γ nat
    rec : ∀{C} 
      (e : TExp Γ nat) 
      (eb : TExp Γ C)
      (ei : TExp (C :: nat :: Γ) C)
      → TExp Γ C

  data TVal : TTp → Set where
    Λ_ : ∀{A B} → TExp (A :: []) B → TVal (A ⇒ B)
    true : TVal bool
    false : TVal bool
    z : TVal nat
    s : TVal nat → TVal nat


  -- Denotational syntax

  meanstp : TTp → Set
  meanstp nat = Nat
  meanstp bool = Bool
  meanstp (A ⇒ B) = meanstp A -> meanstp B

  meansctx : List TTp → Set
  meansctx [] = ⊤
  meansctx (A :: Γ) = meanstp A × meansctx Γ

  meansexp : ∀{A Γ}
    → TExp Γ A 
    → meansctx Γ 
    → meanstp A
  meansexp {A} (var x) γ = loop x γ
   where 
    loop : ∀{Γ'} → A ∈ Γ' → meansctx Γ' → meanstp A
    loop Z (e , _) = e
    loop (S n) (_ , γ) = loop n γ
  meansexp (Λ e) γ = λ x → meansexp e (x , γ)
  meansexp (e₁ · e₂) γ = meansexp e₁ γ (meansexp e₂ γ)
  meansexp true γ = True
  meansexp false γ = False
  meansexp {A} (ite e et ef) γ = 
    if (λ _ → meanstp A) / meansexp e γ 
    then (meansexp et γ)
    else (meansexp ef γ)
  meansexp z γ = Z
  meansexp (s e) γ = S (meansexp e γ)
  meansexp {A} (rec e eb ei) γ = 
    NAT.fold {λ _ → meanstp A} (meansexp eb γ)
      (λ n x → meansexp ei (x , n , γ))
      (meansexp e γ)

  meansval : ∀{A} → TVal A → meanstp A
  meansval (Λ y) = λ x → meansexp y (x , <>)
  meansval true = True
  meansval false = False
  meansval z = Z
  meansval (s y) = S (meansval y)


  -- Operational semantics
  
  wk : ∀{Γ Γ' A} → Γ ⊆ Γ' → TExp Γ A → TExp Γ' A
  wk θ (var x) = var (θ x)
  wk θ (Λ e) = Λ wk (LIST.SET.sub-cons-congr θ) e
  wk θ (e₁ · e₂) = wk θ e₁ · wk θ e₂
  wk θ true = true
  wk θ false = false
  wk θ (ite e et ef) = ite (wk θ e) (wk θ et) (wk θ ef)
  wk θ z = z
  wk θ (s e) = s (wk θ e)
  wk θ (rec e eb ei) = 
    rec (wk θ e) (wk θ eb) (wk (LIST.SET.sub-append-congr (_ :: _ :: []) θ) ei)

  subst : ∀{Γ A C} (Γ' : List TTp)
    → TExp Γ A
    → TExp (Γ' ++ A :: Γ) C
    → TExp (Γ' ++ Γ) C
  subst [] e' (var Z) = e'
  subst [] e' (var (S n)) = var n
  subst (_ :: Γ') e' (var Z) = var Z
  subst (_ :: Γ') e' (var (S n)) = wk LIST.SET.sub-cons (subst Γ' e' (var n))
  subst Γ' e' (Λ e) = Λ subst (_ :: Γ') e' e
  subst Γ' e' (e₁ · e₂) = subst Γ' e' e₁ · subst Γ' e' e₂
  subst Γ' e' true = true
  subst Γ' e' false = false
  subst Γ' e' (ite e et ef) = 
    ite (subst Γ' e' e) (subst Γ' e' et) (subst Γ' e' ef)
  subst Γ' e' z = z
  subst Γ' e' (s e) = s (subst Γ' e' e)
  subst Γ' e' (rec e eb ei) = 
    rec (subst Γ' e' e) (subst Γ' e' eb) (subst (_ :: _ :: Γ') e' ei)

  data TRes : TTp → Set where
    Step : ∀{A} → TExp [] A → TRes A
    Value : ∀{A} → TVal A → TRes A

  encodeNE : Nat → TExp [] nat
  encodeNE Z = z
  encodeNE (S y) = s (encodeNE y)

  step : ∀{A} → TExp [] A → TRes A 
  step (var ())
  step (Λ e) = Value (Λ e)
  step (e₁ · e₂) with step e₁
  ... | Step e₁' = Step (e₁' · e₂)
  ... | Value (Λ e₀) = Step (subst [] e₂ e₀)
  step true = Value true
  step false = Value false
  step (ite e et ef) with step e
  ... | Step e' = Step (ite e' et ef)
  ... | Value true = Step et
  ... | Value false = Step ef
  step z = Value z
  step (s e) with step e
  ... | Step e' = Step (s e')
  ... | Value n = Value (s n)
  step {A} (rec e eb ei) with step e
  ... | Step e' = Step (rec e' eb ei)
  ... | Value n = 
    Step (NAT.fold {λ _ → TExp [] A} eb
           (λ n' x → subst [] x (subst (_ :: []) (encodeNE n') ei))  
           (meansval n))


  -- Steps preserve meaning

  meansres : ∀{A} → TRes A → meanstp A
  meansres (Step e) = meansexp e <>
  meansres (Value v) = meansval v

  pres : ∀{A} (e : TExp [] A) → Id (meansexp e <>) (meansres (step e))
  pres (var ())
  pres (Λ e) = refl
  pres (e₁ · e₂) with pres e₁
  pres (e₁ · e₂) | eq with step e₁ 
  ... | Step e₁' = resp (λ x → x (meansexp e₂ <>)) eq 
  ... | Value (Λ e₀) =
    trans (resp (λ x → x (meansexp e₂ <>)) eq)
      ({!!})
  pres true = refl
  pres false = refl
  pres (ite e et ef) with pres e
  pres {A} (ite e et ef) | eq with step e
  ... | Step e' = 
    resp (λ x → if (λ _ → meanstp A) / x
                then (meansexp et <>) 
                else (meansexp ef <>)) eq
  ... | Value true = 
    resp (λ x → if (λ _ → meanstp A) / x
                then (meansexp et <>) 
                else (meansexp ef <>)) eq
  ... | Value false = 
    resp (λ x → if (λ _ → meanstp A) / x
                then (meansexp et <>) 
                else (meansexp ef <>)) eq
  pres z = refl
  pres (s e) with pres e
  pres (s e) | eq with step e
  ... | Step e' = resp (λ x → S x) eq
  ... | Value v = resp (λ x → S x) eq
  pres (rec e eb ei) with pres e 
  pres (rec e eb ei) | eq with step e 
  ... | Step e' = 
    resp (λ x → NAT.fold (meansexp eb <>) 
                  (λ n x' → meansexp ei (x' , n , <>)) x) eq 
  ... | Value v =
    {! resp (λ x → NAT.fold (meansexp eb <>) 
                  (λ n x' → meansexp ei (x' , n , <>)) x) eq !}
--   where
--    loop
--     ∀{n m} → n ≡ m → Nat.fo
