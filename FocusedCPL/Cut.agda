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

  

  Evidence : MCtx → MCtx → Set
  Evidence Γ Γ' = 
    LIST.All (λ Item → Term [] Γ (prjw Item) · (Reg (↑ (prjx Item)))) Γ'

  P : W → Set
  P _ = Unit

  subst⁺ : (wc : W) → ((wc' : W) → wc ≺+ wc' → P wc') → ∀{Γ w A C ω}
    → Value [] Γ w A
    → Term [] Γ wc (I A w ω) (Reg C)
    → Term [] Γ wc · (Reg C)

  subst⁻ : (wc : W) → ((wc' : W) → wc ≺+ wc' → P wc') → ∀{Γ w A C ω} 
    → Term [] Γ w · (Reg A)
    → Spine [] Γ w A wc ω (Reg C)
    → Term [] Γ wc · (Reg C)

  rsubstV : (wc : W) → ((wc' : W) → wc ≺+ wc' → P wc') → ∀{Γ w A C}
    (Γ' : MCtx)
    → Evidence Γ Γ'
    → Term [] Γ w · (Reg A)
    → Value [] (Γ' ++ ↓ A at w :: Γ) wc C
    → Value [] (Γ' ++ Γ) wc C

  rsubstN : (wc : W) → ((wc' : W) → wc ≺+ wc' → P wc') → ∀{Γ w A C Ω} 
    (Γ' : MCtx)
    → Evidence Γ Γ'
    → Term [] Γ w · (Reg A)
    → Term [] (Γ' ++ ↓ A at w :: Γ) wc Ω (Reg C)
    → Term [] (Γ' ++ Γ) wc Ω (Reg C)

  rsubstSp : (wc : W) → ((wc' : W) → wc ≺+ wc' → P wc') → ∀{Γ w wh ωh A B C} 
    (Γ' : MCtx)
    → Evidence Γ Γ'
    → Term [] Γ w · (Reg A)
    → Spine [] (Γ' ++ ↓ A at w :: Γ) wh B wc ωh (Reg C)
    → Spine [] (Γ' ++ Γ) wh B wc ωh (Reg C)

  subst⁺ wc ih (pR x) (L pf⁺ N₁) = {! -- contraction --!}
  subst⁺ wc ih (↓R N₁) (L pf⁺ N₁')  = {!!}
  subst⁺ wc ih (◇R wh N₁) (L () N₁')
  subst⁺ wc ih (◇R wh N₁) (◇L N₁') = N₁' wh N₁
  subst⁺ wc ih (□R N₁) (L () N₁')
  subst⁺ wc ih (□R N₁) (□L N₁') = N₁' (λ ω → N₁ ω)

  subst⁻ wc ih (↓L pf⁻ ωh x Sp) pL = {!!}
  subst⁻ wc ih (↓L pf⁻ ωh x Sp) (↑L N₁) = {!!}
  subst⁻ wc ih (↓L () ωh x Sp) (⊃L V₁ Sp₂)
  subst⁻ wc ih (↑R V₁) (↑L N₁) = subst⁺ wc ih V₁ N₁
  subst⁻ wc ih {ω = ≺*≡} (⊃R N₁) (⊃L V₁ Sp₂) = 
    subst⁻ wc ih  (subst⁺ wc ih V₁ N₁) Sp₂
  subst⁻ wc ih {ω = ≺*+ ω} (⊃R N₁) (⊃L V₁ Sp₂) = 
    subst⁻ wc ih {! CUT: V₁ N₁!} Sp₂

  rsubstV wc ih Γ' γ N (pR x) with fromctx Γ' x
  ... | Inl ()
  ... | Inr x' = pR x'
  rsubstV wc ih Γ' γ N (↓R N₁) = ↓R (rsubstN wc ih Γ' γ N N₁)
  rsubstV wc ih Γ' γ N (CORE.◇R wh N₁) = ◇R wh {! CUT: N N₁!}
  rsubstV wc ih Γ' γ N (CORE.□R N₁) = □R λ ω' → {! CUT: N N₁!}

  rsubstN wc ih Γ' γ N (L pf⁺ N₁) = L pf⁺ (rsubstN wc ih (_ :: Γ') {!!} N N₁)
  rsubstN wc ih Γ' γ N (↓L pf⁻ ωh x Sp) with fromctx Γ' x
  ... | Inl Refl = subst⁻ wc ih {! weakened N!} (rsubstSp wc ih Γ' γ N Sp)
  ... | Inr x' = ↓L pf⁻ ωh x' (rsubstSp wc ih Γ' γ N Sp)
  rsubstN wc ih Γ' γ N ⊥L = ⊥L
  rsubstN wc ih Γ' γ N (◇L N₁) = 
    ◇L λ ω' N₀ → rsubstN wc ih Γ' γ N (N₁ ω' {! DECUT: N₀!})
  rsubstN wc ih Γ' γ N (□L N₁) = 
    □L λ N₀ → rsubstN wc ih Γ' γ N (N₁ λ ω' → {! DECUT: N₀ ω'!})
  rsubstN wc ih Γ' γ N (↑R V₁) = ↑R (rsubstV wc ih Γ' γ N V₁)
  rsubstN wc ih Γ' γ N (⊃R N₁) = ⊃R (rsubstN wc ih Γ' γ N N₁)

  rsubstSp wc ih Γ' γ N Sp = {!!}

