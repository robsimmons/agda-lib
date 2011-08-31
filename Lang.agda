

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

  data Exp (Δ : VCtx) : CType → Set where
    var : ∀{A} (x : A ∈ Δ) → Exp Δ A
    Λ_ : ∀{A B} (e : Exp (A :: Δ) B) → Exp Δ (A ⇒ B)
    _·_ : ∀{A B} (e₁ : Exp Δ (A ⇒ B)) (e₂ : Exp Δ A) → Exp Δ B
    _[_] : ∀{A Δ'} 
      (p : Norm Δ' [] A)
      (σ : ∀{B} → B ∈ Δ' → Exp Δ B)
      → Exp Δ (F A) 
    elim : ∀{A C}
      (e : Exp Δ (F A))
      (φ : (Δp : VCtx) → Norm Δp [] A → Exp (Δp +>> Δ) C)
      → Exp Δ C

  wk : ∀{Δ Δ' A} → Δ ⊆ Δ' → Exp Δ A → Exp Δ' A
  wk θ (var x) = var (θ x)
  wk θ (Λ e) = Λ wk (LIST.SET.sub-cons-congr θ) e
  wk θ (e₁ · e₂) = wk θ e₁ · wk θ e₂
  wk θ (p [ σ ]) = p [ (λ x → wk θ (σ x)) ]
  wk θ (elim e φ) = elim (wk θ e) 
    λ Δp N → wk (sub-revappend-congr Δp θ) (φ Δp N)

  subst : ∀{Δ A C} (Δ' : VCtx)
    → Exp Δ A
    → Exp (Δ' ++ A :: Δ) C 
    → Exp (Δ' ++ Δ) C  
  subst [] e' (var Z) = e'
  subst [] e' (var (S n)) = var n
  subst (B :: Δ') e' (var Z) = var Z
  subst (B :: Δ') e' (var (S n)) = wk LIST.SET.sub-cons (subst Δ' e' (var n))
  subst Δ' e' (Λ e) = Λ subst (_ :: Δ') e' e
  subst Δ' e' (e₁ · e₂) = subst Δ' e' e₁ · subst Δ' e' e₂
  subst Δ' e' (p [ σ ]) = p [ (λ x → subst Δ' e' (σ x)) ]
  subst Δ' e' (elim e φ) = elim (subst Δ' e' e) 
    λ Δp x → loop Δp Δ' e' (φ Δp x)
   where 
    loop : ∀{Δ A C} (Δp Δ' : VCtx)
      → Exp Δ A
      → Exp (Δp +>> (Δ' ++ A :: Δ)) C
      → Exp (Δp +>> (Δ' ++ Δ)) C
    loop [] Δ' e' e = subst Δ' e' e
    loop (_ :: Δp) Δ' e' e = loop Δp (_ :: Δ') e' e

  data Val : CType → Set where
    VLam : ∀{A B}
      (e : Exp (A :: []) B)
      → Val (A ⇒ B)
    VDat : ∀{A Δ'} →
      (p : Norm Δ' [] A)
      (σ : ∀{B} → B ∈ Δ' → Exp [] B)
      → Val (F A) 

  data Res : CType → Set where
    Step : ∀{A} → Exp [] A → Res A 
    Value : ∀{A} → Val A → Res A

  step : ∀{A} → Exp [] A → Res A
  step (var ())
  step (Λ e) = Value (VLam e)
  step (e₁ · e₂) with step e₁
  ... | Step e₁' = Step (e₁' · e₂)
  ... | Value (VLam e₀) = Step (subst [] e₂ e₀)
  step (p [ σ ]) = Value (VDat p σ)
  step (elim e φ) = {!!}
