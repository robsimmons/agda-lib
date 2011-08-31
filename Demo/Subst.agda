{- Creating a simultaneous substitution as a LIST.ALL list -}

module Demo.Subst where

open import Prelude

-- Types for PCF
data Type : Set where
  nat : Type
  _⊃_ : Type → Type → Type

Context : Set
Context = List Type

-- Terms for PCF
data Term : Context → Type → Set where
  var   : ∀{Δ t} → t ∈ Δ → Term Δ t
  z     : ∀{Δ} → Term Δ nat
  s     : ∀{Δ} → Term Δ nat → Term Δ nat
  if    : ∀{Δ t} → Term Δ nat → Term Δ t → Term Δ (nat ⊃ t) → Term Δ t
  fix   : ∀{Δ t} → Term Δ (t ⊃ t) → Term Δ t
  lam   : ∀{Δ t s} → Term (t :: Δ) s → Term Δ (t ⊃ s)
  app   : ∀{Δ t s} → Term Δ (t ⊃ s) → Term Δ t → Term Δ s
  
Subst : Context → Context → Set
Subst Γ Δ = LIST.All (λ t → Term Δ t) Γ

wken : ∀{Γ Δ t} → LIST.SET.Sub Γ Δ → Term Γ t → Term Δ t
wken θ (var n) = var (θ n)
wken θ z = z
wken θ (s e) = s (wken θ e)
wken θ (if e ez es) = if (wken θ e) (wken θ ez) (wken θ es)
wken θ (fix e) = fix (wken θ e)
wken θ (lam e) = lam (wken (LIST.SET.sub-cons-congr θ) e)
wken θ (app e1 e2) = app (wken θ e1) (wken θ e2)

subst : ∀{Γ Δ t} → Subst Γ Δ → Term Γ t → Term Δ t
subst θ (var n) = LIST.ALL.pull n θ
subst θ z = z
subst θ (s e) = s (subst θ e)
subst θ (if e ez es) = if (subst θ e) (subst θ ez) (subst θ es)
subst θ (fix e) = fix (subst θ e)
subst θ (lam e) = lam (subst 
   (LIST.case-cons (Term _) (var Z) (wken LIST.SET.sub-cons o θ)) e)
subst θ (app e1 e2) = app (subst θ e1) (subst θ e2)