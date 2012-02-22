open import Prelude hiding (Level)
import Adjoint

module AdjointCut 
  (Level : Set)
  (True : Level)
  (_≤_ : Level → Level → Set)
  (refl≤ : (L : Level) → L ≤ L)
  (trans≤ : ∀{L1 L2 L3} → L1 ≤ L2 → L2 ≤ L3 → L1 ≤ L3)
  (truth : (L : Level) → True ≤ L)
  (dec≤ : (L1 L2 : Level) → Decidable (L1 ≤ L2)) where

open Adjoint Level True _≤_ refl≤ trans≤ truth dec≤

-- Substitution

subst⁺ : ∀{Γ A L C}
  → Value [] (clear Γ L) (A , L)
  → Case [] Γ (A , L) (Reg C)
  → Term [] Γ (Reg C)

subst⁻ : ∀{Γ A C}
  → Reg C stable⁻
  → Term [] Γ (Reg A)
  → Spine [] Γ A (Reg C)
  → Term [] Γ (Reg C)

{-

substV : ∀{Γ A H} (Γ' : Ctx)
  → Term [] (Γ' ++ Γ) (Reg A)
  → Value [] (Γ' ++ (↓ A) :: Γ) H
  → Value [] (Γ' ++ Γ) H
-}

rsubstN : ∀{Γ A C L} (Γ' : Ctx)
  → Term [] (clear (Γ' ++ Γ) L) (Reg A)
  → Term [] (Γ' ++ (↓ A , L) :: Γ) (Reg C)
  → Term [] (Γ' ++ Γ) (Reg C)

{-
substNI : ∀{Γ A H C} (Γ' : Ctx)
  → Term [] (Γ' ++ Γ) (Reg A)
  → Case [] (Γ' ++ (↓ A) :: Γ) H (Reg C)
  → Case [] (Γ' ++ Γ) H (Reg C)

substSp : ∀{Γ A B C} (Γ' : Ctx)
  → Term [] (Γ
-}

subst⁺ (hyp⁺ ()) N
subst⁺ (pR x) (L pf⁺ N) = wk (LIST.SET.sub-cntr (snd (inclear-necc x))) N
subst⁺ (↓R N) (L pf⁺ N') = rsubstN [] N N'
subst⁺ {Γ} (!R pf≤ V) (!L NI) = subst⁺ (wk (clearer' {Γ} pf≤) V) (NI pf≤)
subst⁺ (!R pf≤ V) (L () N)

subst⁻ pf (↓L pf⁻ x Sp) pL = ↓L pf⁻ x Sp
subst⁻ pf (↓L pf⁻ x Sp) (↑L NI) = {!↓L pf ? !} -- ↓L pf ? ? 
subst⁻ pf (↓L () x Sp) (⊃L V Sp')
subst⁻ pf (↓L () x Sp) (∧⁻L₁ Sp')
subst⁻ pf (↓L () x Sp) (∧⁻L₂ Sp')
subst⁻ pf (↑R V) (↑L NI) = subst⁺ (wk {!!} V) NI
subst⁻ pf (⊃R NI) (⊃L V Sp) = subst⁻ pf (subst⁺ ? NI) Sp
subst⁻ pf ⊤⁻R M = {!!}
subst⁻ pf (∧⁻R N₁ N₂) M = {!!}

rsubstN = {!!}