

module Lang where

open import Prelude hiding ([_])
open import Lambda

module LANG (Atom : Set ; Const : Set ; sig : Const → TYPES.VType Atom ⁻) where
  
  open TYPES Atom
  open TERMS Atom Const sig renaming (wk to wkN)

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
      (φ : (Δ' : VCtx) → Norm Δ' [] A → Exp (Δ' ++ Δ) C)
      → Exp Δ C

  wk : ∀{Δ Δ' A} → Δ ⊆ Δ' → Exp Δ A → Exp Δ' A
  wk θ (var x) = var (θ x)
  wk θ (Λ e) = Λ wk (LIST.SET.sub-cons-congr θ) e
  wk θ (e₁ · e₂) = wk θ e₁ · wk θ e₂
  wk θ (p [ σ ]) = p [ (λ x → wk θ (σ x)) ]
  wk θ (elim e φ) = elim (wk θ e) (λ Δ' N → wk {!LIST.SET.sub-append-congr Δ'!} (φ Δ' N))