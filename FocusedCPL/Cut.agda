open import Prelude hiding (⊥; [_])
open import Accessibility.Inductive
open import Accessibility.IndexedList
open import FocusedCPL.Core 

module FocusedCPL.Cut where

module SEQUENT-CUT (UWF : UpwardsWellFounded) where

  open TRANS-UWF UWF
  open ILIST UWF
  open CORE UWF

  fromctx : ∀{A w Item Γ} (Γ' : MCtx) 
    → Item ∈ (Γ' ++ (A at w) :: Γ) 
    → (Item ≡ (A at w)) + (Item ∈ (Γ' ++ Γ))
  fromctx [] Z = Inl Refl 
  fromctx [] (S x) = Inr x
  fromctx (A :: Γ') Z = Inr Z
  fromctx (A :: Γ') (S x) with fromctx Γ' x
  ... | Inl Refl = Inl Refl
  ... | Inr x' = Inr (S x')

  P : W → Set
  P _ = Unit

  subst⁺ : (wc : W) → ((wc' : W) → wc ≺+ wc' → P wc') → ∀{Γ w A C ω}
    → Value [] Γ w A
    → Term [] Γ wc (I A w ω) (Reg C)
    → Term [] Γ wc · (Reg C)

  rsubstN : (wc : W) → ((wc' : W) → wc ≺+ wc' → P wc') → ∀{Γ w A C Ω} 
    (Γ' : MCtx)
    → wc ≺* w
    → Term [] Γ w · (Reg A)
    → Term [] (Γ' ++ ↓ A at w :: Γ) wc Ω (Reg C)
    → Term [] (Γ' ++ Γ) wc Ω (Reg C)

  subst⁺ wc ih (CORE.pR x) (CORE.L pf⁺ N₁) = {!-- weakening --!}
  subst⁺ wc ih (CORE.↓R N₁) (CORE.L pf⁺ N₁')  = {!!}
  subst⁺ wc ih (CORE.◇R wh N₁) (CORE.L () N₁')
  subst⁺ wc ih (CORE.◇R wh N₁) (CORE.◇L N₁') = N₁' wh N₁
  subst⁺ wc ih (CORE.□R N₁) (CORE.L () N₁')
  subst⁺ wc ih (CORE.□R N₁) (CORE.□L N₁') = N₁' (λ ω → N₁ ω)

  rsubstN wc ih Γ' ω N (CORE.L pf⁺ N₁) = 
    L pf⁺ (rsubstN wc ih (_ :: Γ') ω N N₁)
  rsubstN wc ih Γ' ω N (CORE.↓L pf⁻ ωh x Sp) with fromctx Γ' x
  ... | Inl Refl = {!!}
  ... | Inr x' = ↓L pf⁻ ωh x' {!↓L pf⁻!}
  rsubstN wc ih Γ' ω N CORE.⊥L = ⊥L
  rsubstN wc ih Γ' ω N (CORE.◇L N₁) = 
    ◇L λ ω' N₀ → rsubstN wc ih Γ' ω N (N₁ ω' {! DECUT: N₀!})
  rsubstN wc ih Γ' ω N (CORE.□L N₁) = 
    □L λ N₀ → rsubstN wc ih Γ' ω N (N₁ λ ω' → {! DECUT: N₀ ω'!})
  rsubstN wc ih Γ' ω N (CORE.⊃R N₁) = ⊃R (rsubstN wc ih Γ' ω N N₁)

  