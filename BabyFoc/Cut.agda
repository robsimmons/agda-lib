
open import Prelude hiding (⊥; ⊤)
open import BabyFoc.Foc

module BabyFoc.Cut where

lsubst : ∀{A Γ C}
  → Reg C stable
  → Term [] Γ (Reg A) 
  → Spine [] Γ A (Reg C) 
  → Term [] Γ (Reg C)

-- either : ∀{A B Γ} (Γ' : Ctx) → B ∈ (Γ' ++ A :: Γ) → (A ≡ B) + 

rsubst : ∀{Γ A Form} (Γ' : Ctx)
  → (Term [] Γ (Reg A) + Value [] Γ A)
  → Exp [] (Γ' ++ A :: Γ) Form
  → Exp [] (Γ' ++ Γ) Form

-- subst⁺ : ∀{Γ A C} → Value [] Γ A → Term [] (A :: Γ) (Reg C) → Term [] Γ (Reg C)

lsubst pf (foc pf₁ x pf₂ Sp) Sp' = {!Sp'!}
lsubst pf (⊥L x) Sp = {!!}
lsubst pf (∨L x N₁ N₂) Sp = {!!}
lsubst pf (⊤L x N) Sp = {!!}
lsubst pf (rfoc () V) pL
lsubst pf (rfoc pf' V) (↑L pf'' N) = rsubst [] (Inr V) N
lsubst pf (rfoc () V) (⊃L V' Sp)
lsubst pf (⊃R N) (↑L () N')
lsubst pf (⊃R N) (⊃L V Sp) = lsubst pf (rsubst [] (Inr V) N) Sp

rsubst Γ' N (foc pf₁ x pf₂ Sp) = {!!}
rsubst Γ' N (hyp⁺ ())
rsubst Γ' N (pR x) = {!!}
rsubst Γ' N (↓R pf N') = ↓R pf (rsubst Γ' N N')
rsubst Γ' N (∨R₁ V) = ∨R₁ (rsubst Γ' N V)
rsubst Γ' N (∨R₂ V) = ∨R₂ (rsubst Γ' N V)
rsubst Γ' N ⊤R = ⊤R

rsubst Γ' N (⊥L x) = {! -- finish --!}
rsubst Γ' N (∨L x N₁ N₂) = {! -- check for critical case --!}
rsubst Γ' N (⊤L x N') = {! -- don't actually care but whatever --!}
rsubst Γ' N (rfoc pf V) = rfoc pf (rsubst Γ' N V)
rsubst Γ' N (⊃R N') = ⊃R (rsubst (_ :: Γ') N N')

rsubst Γ' N hyp⁻ = hyp⁻
rsubst Γ' N pL = pL
rsubst Γ' N (↑L pf N') = ↑L pf (rsubst (_ :: Γ') N N')
rsubst Γ' N (⊃L V Sp) = ⊃L (rsubst Γ' N V) (rsubst Γ' N Sp)
