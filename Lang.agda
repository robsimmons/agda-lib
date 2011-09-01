

module Lang where

open import Prelude hiding ([_])
open import Lambda

module LANG (Atom : Set ; Const : Set ; sig : Const → TYPES.VType Atom ⁻) where
  
  open TYPES Atom
  open TERMS Atom Const sig renaming (wk to wkN ; subst to substN)

  _+>>_ : {A : Set} → List A → List A → List A
  [] +>> Δ = Δ
  (A :: Δ') +>> Δ = Δ' +>> (A :: Δ)
 
  sub-revappendl : {A : Set} 
      → (xs : List A)
      → (ys : List A)
      → LIST.SET.Sub xs (ys +>> xs)
  sub-revappendl xs [] n = n
  sub-revappendl xs (x :: ys) n = sub-revappendl (x :: xs) ys (S n)

  sub-revappendl' : {A : Set} {xs1 xs2 : List A}
      → (ys : List A)
      → LIST.SET.Sub xs1 xs2
      → LIST.SET.Sub xs1 (ys +>> xs2)
  sub-revappendl' ys f x = sub-revappendl _ ys (f x)    

  sub-revappend-congr : {A : Set} {xs2 ys2 : List A}
      (xs : List A)
      → LIST.SET.Sub xs2 ys2
      → LIST.SET.Sub (xs +>> xs2) (xs +>> ys2)
  sub-revappend-congr [] f = f
  sub-revappend-congr (x :: xs) f = 
      sub-revappend-congr xs (LIST.SET.sub-cons-congr f)

  mutual
    data Exp (Γ : VCtx) : CType → Set where
      var : ∀{A} (x : A ∈ Γ) → Exp Γ A
      Λ_ : ∀{A B} (e : Exp (A :: Γ) B) → Exp Γ (A ⇒ B)
      _·_ : ∀{A B} (e₁ : Exp Γ (A ⇒ B)) (e₂ : Exp Γ A) → Exp Γ B
      _[_] : ∀{A Δ} 
        (p : Norm Δ [] A)
        (σ : Subst Γ Δ)
        → Exp Γ (F A) 
      elim : ∀{A C}
        (e : Exp Γ (F A))
        (φ : ∀{Δp} (N : Norm Δp [] A) → Exp (Δp +>> Γ) C)
        → Exp Γ C

    data Subst (Γ : VCtx) : VCtx → Set where
      ⟨⟩ : Subst Γ []
      _,_ : ∀{A Δ}
        (e : Exp Γ A)
        (σ : Subst Γ Δ)
        → Subst Γ (A :: Δ)

  mutual 
    wk : ∀{Γ Γ' A} → Γ ⊆ Γ' → Exp Γ A → Exp Γ' A
    wk θ (var x) = var (θ x)
    wk θ (Λ e) = Λ wk (LIST.SET.sub-cons-congr θ) e  
    wk θ (e₁ · e₂) = wk θ e₁ · wk θ e₂
    wk θ (p [ σ ]) = p [ wkσ θ σ ]
    wk θ (elim e φ) = elim (wk θ e) 
      (λ {Δp} N → wk (sub-revappend-congr Δp θ) (φ N))

    wkσ : ∀{Γ Γ' Δ} → Γ ⊆ Γ' → Subst Γ Δ → Subst Γ' Δ
    wkσ θ ⟨⟩ = ⟨⟩
    wkσ θ (e , σ) = wk θ e , wkσ θ σ 

  -- Pull a term out of a substitution
  σ→ : ∀{Γ Δ A} → A ∈ Δ → Subst Γ Δ → Exp Γ A
  σ→ () ⟨⟩
  σ→ Z (N , σ) = N
  σ→ (S x) (N , σ) = σ→ x σ

  -- Check to see where a variable lives in the context
  Γ? : ∀{Γ Δ B} (Γ' : VCtx)
    → Subst Γ Δ 
    → B ∈ Γ' ++ Δ +>> Γ
    → (B ∈ Δ) + (B ∈ Γ' ++ Γ)
  Γ? [] ⟨⟩ x = Inr x
  Γ? [] (M , σ) x with Γ? [] (wkσ LIST.SET.sub-wken σ) x
  ... | Inl y = Inl (S y) 
  ... | Inr Z = Inl Z
  ... | Inr (S y) = Inr y
  Γ? (B :: Γ') σ Z = Inr Z
  Γ? (_ :: Γ') σ (S x) with Γ? Γ' σ x 
  ... | Inl y = Inl y
  ... | Inr y = Inr (S y) 

  mutual
    subst : ∀{Γ Δ C} (Γ' : VCtx) 
      → Subst Γ Δ
      → Exp (Γ' ++ Δ +>> Γ) C 
      → Exp (Γ' ++ Γ) C  
    subst Γ' τ (var x) with Γ? Γ' τ x 
    ... | Inl y = wk (LIST.SET.sub-appendl _ Γ') (σ→ y τ)
    ... | Inr y = var y
    subst Γ' τ (Λ e) = Λ subst (_ :: Γ') τ e 
    subst Γ' τ (e₁ · e₂) = subst Γ' τ e₁ · subst Γ' τ e₂ 
    subst Γ' τ (p [ σ ]) = p [ substσ Γ' τ σ ]
    subst Γ' τ (elim e φ) = elim (subst Γ' τ e) 
      (λ {Δp} N → loop Δp Γ' τ (φ N)) 
     where
      loop : ∀{Γ Δ C} (Δp Γ' : VCtx)
        → Subst Γ Δ
        → Exp (Δp +>> (Γ' ++ Δ +>> Γ)) C
        → Exp (Δp +>> (Γ' ++ Γ)) C
      loop [] Δ' e' e = subst Δ' e' e
      loop (_ :: Δp) Δ' e' e = loop Δp (_ :: Δ') e' e
      
    substσ : ∀{Γ Δ Δ'} (Γ' : VCtx) 
      → Subst Γ Δ
      → Subst (Γ' ++ Δ +>> Γ) Δ'
      → Subst (Γ' ++ Γ) Δ'
    substσ Γ' τ ⟨⟩ = ⟨⟩
    substσ Γ' τ (e , σ) = subst Γ' τ e , substσ Γ' τ σ

  data Val : CType → Set where
    VLam : ∀{A B}
      (e : Exp (A :: []) B)
      → Val (A ⇒ B)
    VDat : ∀{A Δ} →
      (p : Norm Δ [] A)
      (σ : Subst [] Δ)
      → Val (F A) 

  data Res : CType → Set where
    Step : ∀{A} → Exp [] A → Res A 
    Value : ∀{A} → Val A → Res A

  step : ∀{A} → Exp [] A → Res A
  step (var ())
  step (Λ e) = Value (VLam e)
  step (e₁ · e₂) with step e₁
  ... | Step e₁' = Step (e₁' · e₂)
  ... | Value (VLam e₀) = Step (subst [] (e₂ , ⟨⟩) e₀)
  step (p [ σ ]) = Value (VDat p σ)
  step (elim e φ) with step e
  ... | Step e' = Step (elim e' φ)
  ... | Value (VDat p σ) = Step (subst [] σ (φ p)) 

module TEST-T where  

  data Atom : Set where
    nat : Atom
    bool : Atom

  open TYPES Atom

  data Const : Set where
    true : Const
    false : Const
    z : Const
    s : Const

  sig : Const → VType ⁻
  sig true = con bool
  sig false = con bool
  sig z = con nat
  sig s = U (F (con nat)) ⊃ con nat

  open TERMS Atom Const sig renaming (wk to wkN ; subst to substN)
  open LANG Atom Const sig

{-
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
-}


  data TTp : Set where
    nat : TTp
    bool : TTp
    _⇒_ : (A B : TTp) → TTp

  encode : TTp → CType
  encode nat = F (con nat)
  encode bool = F (con bool)
  encode (A ⇒ B) = encode A ⇒ encode B

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

  

  embed : ∀{Γ A} → TExp Γ A → Lazy (Exp (LIST.map encode Γ) (encode A))
  embed (var x) = thunk (var (LIST.in-map encode x))
  embed (Λ e) = thunk (Λ force (embed e))
  embed (e₁ · e₂) = thunk (force (embed e₁) · force (embed e₂))
  embed true = thunk (⟨ con true refl ⟩ [ ⟨⟩ ])
  embed false = thunk (⟨ con false refl ⟩ [ ⟨⟩ ])
  embed {Γ} {A} (ite e et ef) = 
    thunk 
      (elim (force (embed e))
        (λ {Δp} N → 
          case {A = ⊤} {B = ⊤} (Exp (Δp +>> LIST.map encode Γ) (encode A)) 
            (Inl <>)
            (λ _ → wk (sub-revappendl _ Δp) (force (embed et)))
            (λ _ → wk (sub-revappendl _ Δp) (force (embed ef)))))
  embed z = thunk (⟨ con z refl ⟩ [ ⟨⟩ ])
  embed (s n) = thunk (⟨ con s refl ·' Z ⟩ [ (force (embed n) , ⟨⟩) ])
  embed {Γ} {A} (rec e eb ei) = 
    thunk 
      (elim (force (embed e))
        (λ {Δp} N → 
          case {A = ⊤} {B = Exp (LIST.map encode Γ) (encode nat)} 
            (Exp (Δp +>> LIST.map encode Γ) (encode A)) 
            (Inl <>)
            (λ _ → wk (sub-revappendl _ Δp) (force (embed eb)))
            (λ e → wk (sub-revappendl _ Δp) 
                     (subst [] (e , ({!!} , ⟨⟩)) (force (embed ei))))))

{- 
      (λ {Δp} N → 
        case {A = ⊤} {B = Exp (LIST.map encode Γ) (encode nat)} 
          (Exp (Δp +>> LIST.map encode Γ) (encode A)) 
          (Inl <>)
          (λ <> → wk (sub-revappendl _ Δp) (embed eb))
          (λ e → {! wk (sub-revappendl _ Δp) (embed ef) !})) -}
{-
        if (λ _ → Exp (Δp +>> LIST.map encode Γ) (encode A)) 
        / True 
        then {!!} 
        else {!!}) -}
