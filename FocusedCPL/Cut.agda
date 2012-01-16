{-# OPTIONS --no-termination-check #-}

open import Prelude hiding (⊥)
open import Accessibility.Inductive
open import Accessibility.IndexedList
open import FocusedCPL.Core 
open import FocusedCPL.IH
open import FocusedCPL.Evidence
open import FocusedCPL.Weakening
import FocusedCPL.Decut

module FocusedCPL.Cut (UWF : UpwardsWellFounded)
  (dec≺ : (w w' : _) → Decidable (TRANS-UWF._≺*_ UWF w w')) where

open TRANS-UWF UWF
open ILIST UWF
open SEQUENT UWF
open WEAKENING UWF
open EVIDENCE UWF dec≺
open IH UWF dec≺
open FocusedCPL.Decut UWF dec≺

module SEQUENT-CUT (wc : W) (ih : (wc' : W) → wc ≺+ wc' → P wc') where
  
  -- Ugly evidence-managing lemmas

  weaken-with-evidence-r : ∀{w wh Γ C b} {B : Type ⁺}
    → wc ≺* w
    → EvidenceΩ Γ wc (I B wh) b
    → Term [] Γ w · (Reg C)
    → Term [] ((B at wh) :: Γ) w · (Reg C)
  weaken-with-evidence-r {w} {wh} ω ed N with dec≺ w wh 
  weaken-with-evidence-r ω ed N | Inr ωh =
    wkN <> (⊆to/wkenirrev ωh (⊆to/refl _)) · N
  weaken-with-evidence-r ω ed N | Inl ≺*≡ = 
    wkN <> (⊆to/wken (⊆to/refl _)) · N
  weaken-with-evidence-r ω I≡ N | Inl (≺*+ ωh) = abort (≺+⊀ ωh ω)
  weaken-with-evidence-r ≺*≡ (I+ ωq R) N | Inl (≺*+ ωh) = 
    DECUT.decutN wc ih (N+ ωh R) ·t N
  weaken-with-evidence-r (≺*+ ω) (I+ ωq R) N | Inl (≺*+ ωh) = 
    P.decutN (ih _ ω) (N+ ωh R) ·t N

  weaken-with-evidence-l : ∀{w wh C A B Γ}
    → B stable⁺
    → wc ≺* w
    → EvidenceΩ Γ wc (I B wh) False
    → Term [] ((B at wh) :: Γ) w · (Reg (↑ A))
    → Term [] Γ wc (I A w) (Reg C)
    → Term [] ((B at wh) :: Γ) wc (I A w) (Reg C)
  weaken-with-evidence-l pf ω I≡ N₁ N' = 
    wkN <> (⊆to/wken (⊆to/refl _)) (I ω) N'
  weaken-with-evidence-l pf ≺*≡ (I+ ω' R) N₁ N' = 
    DECUT.decutN wc ih {b = False} (N+ ω' R) I≡ N'
  weaken-with-evidence-l {w} {wh} pf (≺*+ ω) (I+ ω' R) N₁ N' with dec≺ w wh
  ... | Inl ω'' = 
    DECUT.decutN wc ih (N+ ω' R) 
      (I+ ω (Cut (unwind <> ω'' R (↑L (L pf N₁))))) N' 
  ... | Inr ω'' = 
    DECUT.decutN wc ih (N+ ω' R) 
      (I+ ω (Cut (wkN <> (⊆to/stenirrev ω'' (⊆to/refl _)) · N₁))) N'

  decut : ∀{w w' Γ A B C b wh}
    (Γ' : MCtx)
    → EvidenceΩ (Γ' ++ Γ) wc (I C wh) b
    → wh ≺ w
    → Term [] (Γ' ++ Γ) w' · (Reg A)
    → Term [] (Γ' ++ Γ) w · (Reg B)
    → Term [] (Γ' ++ (↓ A at w') :: Γ) w · (Reg B)
  decut {w} {w'} Γ' ed ω N N₀ with evidenceΩ≺ ed | dec≺ w w'
  decut Γ' ed ω N N₀ | _ | Inr ω' = 
    wkN <> 
      (⊆to/trans (⊆to/wkenirrev ω' (⊆to/refl _)) 
        (⊆to/equiv (sub-append-swap [ _ ] Γ' _) (sub-append-swap Γ' [ _ ] _))) 
      · N₀
  decut Γ' ed ω N N₀ | _ | Inl ≺*≡ = 
    wkN <> 
      (⊆to/trans (⊆to/wken (⊆to/refl _)) 
        (⊆to/equiv (sub-append-swap [ _ ] Γ' _) (sub-append-swap Γ' [ _ ] _))) 
      · N₀
  decut Γ' ed ω N N₀ | (I ωed) | Inl (≺*+ ω') = 
    wkN <> 
      (⊆to/equiv (sub-append-swap [ _ ] Γ' _) (sub-append-swap Γ' [ _ ] _))
      · (P.decutN (ih _ (≺*S' ωed ω)) (N+ ω' (Cut (↑R (↓R N)))) ·t N₀)

  -- Main theorem

  subst⁺ : Psubst⁺ wc
  subst⁻ : Psubst⁻ wc
  rsubstV : PrsubstV wc
  rsubstN : PrsubstN wc
  rsubstSp : PrsubstSp wc
  lsubstN : PlsubstN wc
  lsubstSp : PlsubstSp wc

  subst⁺ ω (pR x) (L pf⁺ N₁) = wkN <> (⊆to/cntr x) · N₁
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
  rsubstV Γ' ω N (◇R ω' N₁) = 
    ◇R ω' (P.rsubstN (ih _ (≺+0 ω')) Γ' {! X!} N N₁ ·t)
  rsubstV Γ' ω N (□R N₁) = 
    □R λ ω' → P.rsubstN (ih _ (≺+0 ω')) Γ' {! X!} N (N₁ ω') ·t

  rsubstN Γ' ω N (L pf⁺ N₁) ed = 
    L pf⁺ (rsubstN (_ :: Γ') ω (weaken-with-evidence-r ω ed N) N₁ ·t)
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

  rsubstSp Γ' ω N pL ed = pL
  rsubstSp Γ' ω N (↑L N₁) ed = ↑L (rsubstN Γ' ω N N₁ (atmE ed))
  rsubstSp Γ' ω N (⊃L V₁ Sp₂) ed with (evidenceA≺ ed) 
  ... | ≺*≡ = 
    ⊃L (rsubstV Γ' ω N V₁) 
      (rsubstSp Γ' ω N Sp₂ (appE ed (rsubstV Γ' ω N V₁)))
  ... | ≺*+ ωh'  =
    ⊃L (P.rsubstV (ih _ ωh') Γ' {! X!} N V₁)
      (rsubstSp Γ' ω N Sp₂ (appE ed (P.rsubstV (ih _ ωh') Γ' {! X!} N V₁)))

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
