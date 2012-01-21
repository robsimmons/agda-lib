-- Constructive Provability Logic
-- Focused variant
-- Robert J. Simmons, Bernardo Toninho

-- Main cut proof
{-# OPTIONS --no-termination-check #-}

open import Prelude hiding (⊥)
open import Accessibility.Inductive
open import Accessibility.IndexedList
open import FocusedCPL.Core 
open import FocusedCPL.Weakening
open import FocusedCPL.Atomic
import FocusedCPL.Cut.IH
import FocusedCPL.Cut.Pre

module FocusedCPL.Cut.Main (UWF : UpwardsWellFounded) where
open TRANS-UWF UWF
open FocusedCPL.Cut.IH UWF
open FocusedCPL.Cut.Pre UWF

module MAIN-STEP 
  (dec≺ : (w w' : _) → Decidable (TRANS-UWF._≺*_ UWF w w'))
  (wc : W) (ih : (wc' : W) → wc ≺+ wc' → IH.P dec≺ wc') where
  open ILIST UWF
  open SEQUENT UWF
  open WEAKENING UWF
  open ATOMIC UWF
  open IH dec≺
  open PRE-STEP dec≺ wc ih
  
  subst⁺ : Psubst⁺ wc
  subst⁻ : Psubst⁻ wc
  rsubstV : PrsubstV wc
  rsubstN : PrsubstN wc
  rsubstSp : PrsubstSp wc
  lsubstN : PlsubstN wc
  lsubstSp : PlsubstSp wc

  subst⁺ ω (pR x) (L pf⁺ N₁) = wkN (⊆to/cntr x) · N₁
  subst⁺ ω (↓R N₁) (L pf⁺ N₁')  = rsubstN [] ω N₁ N₁' ·t
  subst⁺ ω (◇R wh N₁) (L () N₁')
  subst⁺ ω (◇R wh N₁) (◇L N₁') = N₁' wh N₁
  subst⁺ ω (□R N₁) (L () N₁')
  subst⁺ ω (□R N₁) (□L N₁') = N₁' (λ ω → N₁ ω)

  subst⁻ pf ω (↓L pf⁻ ωh x Sp) pL = ↓L pf⁻ ωh x Sp
  subst⁻ pf ω (↓L pf⁻ ωh x Sp) (↑L N₁) = 
    ↓L pf (≺*trans ω ωh) x (lsubstSp [] pf ω Sp N₁ (varE x (≺*trans ω ωh)))
  subst⁻ pf ω (↓L () ωh x Sp) (⊃L V₁ Sp₂)
  subst⁻ pf ω (↑R V₁) (↑L N₁) = subst⁺ ω V₁ N₁
  subst⁻ pf ω (⊃R N₁) (⊃L V₁ Sp₂) with ω
  ... | ≺*≡ = subst⁻ pf ω (subst⁺ ω V₁ N₁) Sp₂
  ... | ≺*+ ω' = subst⁻ pf ω (P.subst⁺ (ih _ ω') ≺*≡ V₁ N₁) Sp₂ 

  rsubstV Γ' ω N (pR x) with fromctx Γ' x
  ... | Inl ()
  ... | Inr x' = pR x'
  rsubstV Γ' ω N (↓R N₁) = ↓R (rsubstN Γ' ω N N₁ ·t)
  rsubstV Γ' ω N (◇R ω' N₁) = ◇R ω' (ih-rsubstN (≺+0 ω') Γ' N N₁)
  rsubstV Γ' ω N (□R N₁) = □R λ ω' → ih-rsubstN (≺+0 ω') Γ' N (N₁ ω')

  rsubstN Γ' ω N (L pf⁺ N₁) ed = 
    L pf⁺ (rsubstN (_ :: Γ') ω (weaken-with-evidence-r pf⁺ ω ed N) N₁ ·t)
  rsubstN Γ' ω N (↓L pf⁻ ωh x Sp) ed with fromctx Γ' x
  ... | Inl Refl = subst⁻ pf⁻ ωh N (rsubstSp Γ' ω N Sp (cutE N ωh))
  ... | Inr x' = ↓L pf⁻ ωh x' (rsubstSp Γ' ω N Sp (varE x' ωh))
  rsubstN Γ' ω N ⊥L ed = ⊥L
  rsubstN Γ' ω N (◇L N₁) ed = 
    ◇L λ ω' N₀ → rsubstN Γ' ω N (N₁ ω' (decut Γ' ed ω' N N₀)) ·t
  rsubstN Γ' ω N (□L N₁) ed = 
    □L λ N₀ → rsubstN Γ' ω N (N₁ λ ω' → decut Γ' ed ω' N (N₀ ω')) ·t
  rsubstN Γ' ω N (↑R V₁) ed = ↑R (rsubstV Γ' ω N V₁)
  rsubstN Γ' ω N (⊃R N₁) ed = ⊃R (rsubstN Γ' ω N N₁ I≡)

  --rsubstSp Γ' ω N hyp⁻ ed = hyp⁻
  rsubstSp Γ' ω N pL ed = pL
  rsubstSp Γ' ω N (↑L N₁) ed = ↑L (rsubstN Γ' ω N N₁ (atmE ed))
  rsubstSp Γ' ω N (⊃L V₁ Sp₂) ed with (evidenceA≺ ed) 
  ... | ≺*≡ = 
    ⊃L (rsubstV Γ' ω N V₁) 
      (rsubstSp Γ' ω N Sp₂ (appE ed (rsubstV Γ' ω N V₁)))
  ... | ≺*+ ωh'  =
    ⊃L (ih-rsubstV ωh' Γ' N V₁)
      (rsubstSp Γ' ω N Sp₂ (appE ed (ih-rsubstV ωh' Γ' N V₁)))

  lsubstN Γ' pf ω (L pf⁺ N₁) N' ed =
    L pf⁺ (lsubstN (_ :: Γ') pf ω N₁ 
            (weaken-with-evidence-l pf⁺ ω ed N₁ N') ·f)
  lsubstN Γ' pf ω (↓L pf⁻ ωh x Sp) N' ed = 
    ↓L pf (≺*trans ω ωh) x 
      (lsubstSp Γ' pf ω Sp N' (varE x (≺*trans ω ωh)))
  lsubstN Γ' pf ω ⊥L N' ed = ⊥L
  lsubstN Γ' pf ω (◇L N₁) N' ed = 
    ◇L λ ω' N₀ → lsubstN Γ' pf ω (N₁ ω' N₀) N' ·f
  lsubstN Γ' pf ω (□L N₁) N' ed = 
    □L λ N₀ → lsubstN Γ' pf ω (N₁ λ ω' → N₀ ω') N' ·f
  lsubstN Γ' pf ω (↑R V₁) N' ed = subst⁺ ω V₁ N'

  lsubstSp Γ' pf ω (↑L N₁) N' ed = ↑L (lsubstN Γ' pf ω N₁ N' (atmE ed))
  lsubstSp Γ' pf ω (⊃L V₁ Sp₂) N' ed = 
    ⊃L V₁ (lsubstSp Γ' pf ω Sp₂ N' (appE ed V₁))
