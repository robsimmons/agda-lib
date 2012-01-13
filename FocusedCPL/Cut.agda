-- {-# OPTIONS --no-termination-check #-}

open import Prelude hiding (⊥; [_])
open import Accessibility.Inductive
open import Accessibility.IndexedList
open import FocusedCPL.Core 
open import FocusedCPL.Evidence

module FocusedCPL.Cut where

module SEQUENT-CUT (UWF : UpwardsWellFounded) where

  open TRANS-UWF UWF
  open ILIST UWF
  open CORE UWF
  open EVIDENCE UWF

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

  postulate XXX-HOLE : {A : Set} → String → A

  P : W → Set
  P _ = Unit

  subst⁺ : (wc : W) → ((wc' : W) → wc ≺+ wc' → P wc') → ∀{Γ w A C}
    → wc ≺* w
    → Value [] Γ w A
    → Term [] Γ wc (I A w) (Reg C)
    → Term [] Γ wc · (Reg C)

  subst⁻ : (wc : W) → ((wc' : W) → wc ≺+ wc' → P wc') → ∀{Γ w A C} 
    → (Reg C) stable⁻ 
    → wc ≺* w
    → Term [] Γ w · (Reg A)
    → Spine [] Γ w A wc (Reg C)
    → Term [] Γ wc · (Reg C)

  rsubstV : (wc : W) → ((wc' : W) → wc ≺+ wc' → P wc') → ∀{Γ w A C}
    (Γ' : MCtx)
    → Term [] (Γ' ++ Γ) w · (Reg A)
    → Value [] (Γ' ++ ↓ A at w :: Γ) wc C
    → Value [] (Γ' ++ Γ) wc C

  rsubstN : (wc : W) → ((wc' : W) → wc ≺+ wc' → P wc') → ∀{Γ w A C Ω} 
    (Γ' : MCtx)
    → Term [] (Γ' ++ Γ) w · (Reg A)
    → Term [] (Γ' ++ ↓ A at w :: Γ) wc Ω (Reg C)
    → EvidenceΩ (Γ' ++ Γ) wc Ω 
    → Term [] (Γ' ++ Γ) wc Ω (Reg C)

  rsubstSp : (wc : W) → ((wc' : W) → wc ≺+ wc' → P wc') → ∀{Γ w wh A B C} 
    (Γ' : MCtx)
    → wc ≺* wh
    → Term [] (Γ' ++ Γ) w · (Reg A)
    → Spine [] (Γ' ++ ↓ A at w :: Γ) wh B wc (Reg C)
    → EvidenceA (Γ' ++ Γ) wc B wh
    → Spine [] (Γ' ++ Γ) wh B wc (Reg C)

  lsubstN : (wc : W) → ((wc' : W) → wc ≺+ wc' → P wc') → ∀{Γ w A C Ω} 
    (Γ' : MCtx)
    → (Reg C) stable⁻ 
    → wc ≺* w
    → Term [] (Γ' ++ Γ) w Ω (Reg (↑ A))
    → Term [] (Γ' ++ Γ) wc (I A w) (Reg C)
    → EvidenceΩ (Γ' ++ Γ) wc Ω
    → Term [] (Γ' ++ Γ) wc Ω (Reg C)

  lsubstSp : (wc : W) → ((wc' : W) → wc ≺+ wc' → P wc') → ∀{Γ w A B C wh} 
    (Γ' : MCtx)
    → (Reg C) stable⁻ 
    → wc ≺* w
    → Spine [] (Γ' ++ Γ) wh B w (Reg (↑ A))
    → Term [] (Γ' ++ Γ) wc (I A w) (Reg C)
    → EvidenceA (Γ' ++ Γ) wc B wh
    → Spine [] (Γ' ++ Γ) wh B wc (Reg C)

  subst⁺ wc ih ω (pR x) (L pf⁺ N₁) = XXX-HOLE "easy: contraction on N₁"
  subst⁺ wc ih ω (↓R N₁) (L pf⁺ N₁')  = rsubstN wc ih [] N₁ N₁' ·
  subst⁺ wc ih ω (◇R wh N₁) (L () N₁')
  subst⁺ wc ih ω (◇R wh N₁) (◇L N₁') = N₁' wh N₁
  subst⁺ wc ih ω (□R N₁) (L () N₁')
  subst⁺ wc ih ω (□R N₁) (□L N₁') = N₁' (λ ω → N₁ ω)

  subst⁻ wc ih pf ω (↓L pf⁻ ωh x Sp) pL = ↓L pf⁻ ωh x Sp
  subst⁻ wc ih pf ω (↓L pf⁻ ωh x Sp) (↑L N₁) = 
    ↓L pf (≺*trans ω ωh) x 
      (lsubstSp wc ih [] pf ω Sp N₁ (varE x (≺*trans ω ωh)))
  subst⁻ wc ih pf ω (↓L () ωh x Sp) (⊃L V₁ Sp₂)
  subst⁻ wc ih pf ω (↑R V₁) (↑L N₁) = subst⁺ wc ih ω V₁ N₁
  subst⁻ wc ih pf ω (⊃R N₁) (⊃L V₁ Sp₂) with ω
  ... | ≺*≡ = subst⁻ wc ih pf ω (subst⁺ wc ih ω V₁ N₁) Sp₂
  ... | ≺*+ ω' = subst⁻ wc ih pf ω (XXX-HOLE "RCUT: V₁ N₁") Sp₂ 

  rsubstV wc ih Γ' N (pR x) with fromctx Γ' x
  ... | Inl ()
  ... | Inr x' = pR x'
  rsubstV wc ih Γ' N (↓R N₁) = ↓R (rsubstN wc ih Γ' N N₁ ·)
  rsubstV wc ih Γ' N (CORE.◇R wh N₁) = ◇R wh (XXX-HOLE "RCUT: N N₁")
  rsubstV wc ih Γ' N (CORE.□R N₁) = □R λ ω' → XXX-HOLE "RCUT: N N₁"

  rsubstN wc ih Γ' N (L pf⁺ N₁) ed = 
    L pf⁺ (rsubstN wc ih (_ :: Γ')
            (XXX-HOLE "WEAKEN WITH EVIDENCE 'ed': N") N₁ ·)
  rsubstN wc ih Γ' N (↓L pf⁻ ωh x Sp) ed with fromctx Γ' x
  ... | Inl Refl = 
    subst⁻ wc ih pf⁻ ωh N (rsubstSp wc ih Γ' ωh N Sp (cutE N ωh))
  ... | Inr x' = ↓L pf⁻ ωh x' (rsubstSp wc ih Γ' ωh N Sp (varE x' ωh))
  rsubstN wc ih Γ' N ⊥L ed = ⊥L
  rsubstN wc ih Γ' N (◇L N₁) ed = 
    ◇L λ ω' N₀ → rsubstN wc ih Γ' N (N₁ ω' (XXX-HOLE "DECUT: N₀")) ·
  rsubstN wc ih Γ' N (□L N₁) ed = 
    □L λ N₀ → rsubstN wc ih Γ' N (N₁ λ ω' → XXX-HOLE "DECUT: N₀ ω'") ·
  rsubstN wc ih Γ' N (↑R V₁) ed = ↑R (rsubstV wc ih Γ' N V₁)
  rsubstN wc ih Γ' N (⊃R N₁) ed = ⊃R (rsubstN wc ih Γ' N N₁ I≡)

  rsubstSp wc ih Γ' ωh N pL ed = pL
  rsubstSp wc ih Γ' ωh N (↑L N₁) ed = ↑L (rsubstN wc ih Γ' N N₁ (atmE ed))
  rsubstSp wc ih Γ' ωh N (⊃L V₁ Sp₂) ed with ωh 
  ... | ≺*≡ = 
    ⊃L (rsubstV wc ih Γ' N V₁) 
      (rsubstSp wc ih Γ' ωh N Sp₂ (appE ed (rsubstV wc ih Γ' N V₁)))
  ... | ≺*+ ωh'  =
    ⊃L (XXX-HOLE "CUT: N V₁") 
      (rsubstSp wc ih Γ' ωh N Sp₂ (appE ed (XXX-HOLE "CUT: N V₁")))

  lsubstN wc ih Γ' pf ω (L pf⁺ N₁) N' ed = 
    L pf⁺ (lsubstN wc ih (_ :: Γ') pf ω N₁ 
            (XXX-HOLE "WEAKEN WITH EVIDENCE 'ed': N'") ·)
  lsubstN wc ih Γ' pf ω (↓L pf⁻ ωh x Sp) N' ed = 
    ↓L pf (≺*trans ω ωh) x 
      (lsubstSp wc ih Γ' pf ω Sp N' (varE x (≺*trans ω ωh)))
  lsubstN wc ih Γ' pf ω ⊥L N' ed = ⊥L
  lsubstN wc ih Γ' pf ω (◇L N₁) N' ed = 
    ◇L λ ω' N₀ → lsubstN wc ih Γ' pf ω (N₁ ω' N₀) N' ·
  lsubstN wc ih Γ' pf ω (□L N₁) N' ed = 
    □L λ N₀ → lsubstN wc ih Γ' pf ω (N₁ λ ω' → N₀ ω') N' ·
  lsubstN wc ih Γ' pf ω (↑R V₁) N' ed = subst⁺ wc ih ω V₁ N'

  lsubstSp wc ih Γ' pf ω (↑L N₁) N' ed =
    ↑L (lsubstN wc ih Γ' pf ω N₁ N' (atmE ed))
  lsubstSp wc ih Γ' pf ω (⊃L V₁ Sp₂) N' ed = 
    ⊃L V₁ (lsubstSp wc ih Γ' pf ω Sp₂ N' (appE ed V₁))