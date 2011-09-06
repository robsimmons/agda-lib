module LangT where

open import Prelude hiding ([_])
open import Lambda
open import Lang

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

  data TVal : TTp → Set where
    Λ_ : ∀{A B} → TExp (A :: []) B → TVal (A ⇒ B)
    true : TVal bool
    false : TVal bool
    z : TVal nat
    s : TVal nat → TVal nat

  data TRes : TTp → Set where
    Step : ∀{A} → TExp [] A → TRes A
    Value : ∀{A} → TVal A → TRes A

  decodeNV : TVal nat → Nat
  decodeNV z = Z
  decodeNV (s y) = S (decodeNV y)

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
           (decodeNV n))


  -- Denotational syntax

  meanstp : TTp → Set
  meanstp nat = Nat
  meanstp bool = Bool
  meanstp (A ⇒ B) = meanstp A -> meanstp B

  meansctx : List TTp → Set
  meansctx [] = ⊤
  meansctx (A :: Γ) = meanstp A × meansctx Γ

  meansexp : ∀ {A Γ}
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

module LANG-T where


  data Atom : Set where
    nat : Atom
    bool : Atom

  open TYPES Atom public

  data Const : Set where
    true : Const
    false : Const
    z : Const
    s : Const

  sig : Const → VType ⁻
  sig true = con bool
  sig false = con bool
  sig z = con nat
  sig s = ⟨ con nat ⟩ ⊃ con nat

  open TERMS Atom Const sig public renaming (wk to wkN ; subst to substN) 
  open LANG Atom Const sig public 

  abort₁ : ∀{Δ A B C} {Any : Set} → Neut Δ [] (A ⊃ B ⊃ C) → Any
  abort₁ (var ()) 
  abort₁ (R ·' x) = abort₁ R
  abort₁ (con true ())
  abort₁ (con false ())
  abort₁ (con z ())
  abort₁ (con s ()) 
  abort₁ (R · N) = abort₁ R

  abort₂ : ∀{Δ A B} {Any : Set} → Neut Δ [] (U A ⊃ B) → Any
  abort₂ (var ())
  abort₂ (R ·' x) = abort₂ R
  abort₂ (con true ())
  abort₂ (con false ())
  abort₂ (con z ())
  abort₂ (con s ())
  abort₂ (R · N) = abort₁ R

  encodeN : Nat → Norm [] [] (con nat)
  encodeN Z = ⟨ con z refl ⟩
  encodeN (S n) = ⟨ con s refl · encodeN n ⟩

  decodeN : ∀{Γ} → Norm Γ [] (con nat) → Nat
  decodeN ⟨ var () ⟩ 
  decodeN ⟨ R ·' u ⟩ = abort₂ R
  decodeN ⟨ con true () ⟩ 
  decodeN ⟨ con false () ⟩
  decodeN ⟨ con z Refl ⟩ = Z
  decodeN ⟨ con s () ⟩
  decodeN ⟨ var () · N ⟩
  decodeN ⟨ R ·' u · N' ⟩ = abort₂ R
  decodeN ⟨ con true () · N ⟩ 
  decodeN ⟨ con false () · N ⟩
  decodeN ⟨ con z () · N ⟩
  decodeN ⟨ con s Refl · N ⟩ = S (decodeN N)
  decodeN ⟨ R · N · N' ⟩ = abort₁ R

  decodeB : ∀{Γ} → Norm Γ [] (con bool) → Bool
  decodeB ⟨ var () ⟩ 
  decodeB ⟨ R ·' u ⟩ = abort₂ R
  decodeB ⟨ con true Refl ⟩ = True 
  decodeB ⟨ con false Refl ⟩ = False
  decodeB ⟨ con z () ⟩
  decodeB ⟨ con s () ⟩
  decodeB ⟨ var () · N ⟩
  decodeB ⟨ R ·' u · N' ⟩ = abort₂ R
  decodeB ⟨ con true () · N ⟩ 
  decodeB ⟨ con false () · N ⟩
  decodeB ⟨ con z () · N ⟩
  decodeB ⟨ con s () · N ⟩
  decodeB ⟨ R · N · N' ⟩ = abort₁ R




module EQUIV-T where

  open LANG-T 
  open GÖDEL-T renaming (subst to substT ; wk to wkT)

  encode : TTp → CType
  encode nat = F (con nat)
  encode bool = F (con bool)
  encode (A ⇒ B) = encode A ⇒ encode B

  idsub : ∀{Γ} (Δp : VCtx) → Subst (Δp +>> Γ) (Δp)
  idsub [] = ⟨⟩
  idsub (A :: Δp) = var (sub-revappendl _ Δp Z) , idsub Δp

  embed : ∀{Γ A} → TExp Γ A → Exp (LIST.map encode Γ) (encode A)
  embed (var x) = var (LIST.in-map encode x)
  embed (Λ e) = Λ embed e
  embed (e₁ · e₂) = embed e₁ · embed e₂
  embed true = ⟨ con true refl ⟩ [ ⟨⟩ ]
  embed false = ⟨ con false refl ⟩ [ ⟨⟩ ]
  embed {Γ} {A} (ite e et ef) = 
    elim (embed e) 
      (λ {Δp} N → 
        if (λ _ → Exp (Δp +>> LIST.map encode Γ) (encode A)) / decodeB N
        then (wk (sub-revappendl _ Δp) (embed et))
        else (wk (sub-revappendl _ Δp) (embed ef)))
  embed z = ⟨ con z refl ⟩ [ ⟨⟩ ]
  embed (s e) = 
    (Λ elim (var Z) (λ {Δp} N → ⟨ con s refl · N ⟩ [ idsub Δp ])) 
    · embed e
  embed {Γ} {A} (rec e eb ei) = 
    elim (embed e) 
      (λ {Δp} N → 
        NAT.fold {λ _ → Exp (Δp +>> LIST.map encode Γ) (encode A)}
          (wk (sub-revappendl _ Δp) (embed eb)) 
          (λ n x →  
            subst [] ((encodeN n [ ⟨⟩ ]) , x , ⟨⟩) 
              (wk (LIST.SET.sub-cons-congr
                    (LIST.SET.sub-cons-congr (sub-revappendl _ Δp))) 
                (embed ei)))
          (decodeN N))

