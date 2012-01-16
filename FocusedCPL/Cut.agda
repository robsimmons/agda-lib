{-# OPTIONS --no-termination-check #-}

open import Prelude hiding (⊥)
open import Accessibility.Inductive
open import Accessibility.IndexedList
open import FocusedCPL.Core 
open import FocusedCPL.IH
open import FocusedCPL.Evidence
open import FocusedCPL.Weakening

module FocusedCPL.Cut (UWF : UpwardsWellFounded)
  (dec≺ : (w w' : _) → Decidable (TRANS-UWF._≺*_ UWF w w')) where

open TRANS-UWF UWF
open ILIST UWF
open SEQUENT UWF
open EVIDENCE UWF dec≺
open IH UWF
open WEAKENING UWF

fromctx : ∀{A w Item Γ} (Γ' : MCtx) 
  → Item ∈ (Γ' ++ (A at w) :: Γ) 
  → (Item ≡ (A at w)) + (Item ∈ (Γ' ++ Γ))
fromctx [] Z = Inl Refl 
fromctx [] (S x) = Inr x
fromctx (A :: Γ') Z = Inr Z
fromctx (A :: Γ') (S x) with fromctx Γ' x
... | Inl Refl = Inl Refl
... | Inr x' = Inr (S x')  

Psubst⁺ : W → Set
Psubst⁺ wc = ∀{Γ w A C}
    → wc ≺* w
    → Value [] Γ w A
    → Term [] Γ wc (I A w) (Reg C)
    → Term [] Γ wc · (Reg C)

Psubst⁻ : W → Set
Psubst⁻ wc = ∀{Γ w A C} 
    → (Reg C) stable⁻ 
    → wc ≺* w
    → Term [] Γ w · (Reg A)
    → Spine [] Γ w A wc (Reg C)
    → Term [] Γ wc · (Reg C)

PrsubstV : W → Set
PrsubstV wc = ∀{Γ w A C}
    (Γ' : MCtx)
    → wc ≺* w
    → Term [] (Γ' ++ Γ) w · (Reg A)
    → Value [] (Γ' ++ ↓ A at w :: Γ) wc C
    → Value [] (Γ' ++ Γ) wc C

PrsubstN : W → Set
PrsubstN wc = ∀{Γ w A C Ω} 
    (Γ' : MCtx)
    → wc ≺* w
    → Term [] (Γ' ++ Γ) w · (Reg A)
    → Term [] (Γ' ++ ↓ A at w :: Γ) wc Ω (Reg C)
    → EvidenceΩ (Γ' ++ Γ) wc Ω True
    → Term [] (Γ' ++ Γ) wc Ω (Reg C)

PrsubstSp : W → Set
PrsubstSp wc = ∀{Γ w wh A B C} 
    (Γ' : MCtx)
    → wc ≺* w
    → Term [] (Γ' ++ Γ) w · (Reg A)
    → Spine [] (Γ' ++ ↓ A at w :: Γ) wh B wc (Reg C)
    → EvidenceA (Γ' ++ Γ) wc B wh True
    → Spine [] (Γ' ++ Γ) wh B wc (Reg C)

PlsubstN : W → Set
PlsubstN wc = ∀{Γ w A C Ω} 
    (Γ' : MCtx)
    → (Reg C) stable⁻ 
    → wc ≺* w
    → Term [] (Γ' ++ Γ) w Ω (Reg (↑ A))
    → Term [] (Γ' ++ Γ) wc (I A w) (Reg C)
    → EvidenceΩ (Γ' ++ Γ) wc Ω False
    → Term [] (Γ' ++ Γ) wc Ω (Reg C)

PlsubstSp : W → Set
PlsubstSp wc = ∀{Γ w A B C wh} 
    (Γ' : MCtx)
    → (Reg C) stable⁻ 
    → wc ≺* w
    → Spine [] (Γ' ++ Γ) wh B w (Reg (↑ A))
    → Term [] (Γ' ++ Γ) wc (I A w) (Reg C)
    → EvidenceA (Γ' ++ Γ) wc B wh False
    → Spine [] (Γ' ++ Γ) wh B wc (Reg C)

module SEQUENT-CUT (wc : W) (ih : (wc' : W) → wc ≺+ wc' → P wc') where
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
  ... | ≺*+ ω' = subst⁻ pf ω (P.subst⁺ (ih _ ω') V₁ N₁) Sp₂ 

  rsubstV Γ' ω N (pR x) with fromctx Γ' x
  ... | Inl ()
  ... | Inr x' = pR x'
  rsubstV Γ' ω N (↓R N₁) = ↓R (rsubstN Γ' ω N N₁ ·t)
  rsubstV Γ' ω N (◇R ω' N₁) = ◇R ω' (P.rsubstN (ih _ (≺+0 ω')) Γ' N N₁)
  rsubstV Γ' ω N (□R N₁) = □R λ ω' → P.rsubstN (ih _ (≺+0 ω')) Γ' N (N₁ ω')

  rsubstN Γ' ω N (L pf⁺ N₁) ed = 
    L pf⁺ (rsubstN (_ :: Γ') ω (ed-wkN₁ ω ed N) N₁ ·t)
  rsubstN Γ' ω N (↓L pf⁻ ωh x Sp) ed with fromctx Γ' x
  ... | Inl Refl = subst⁻ pf⁻ ωh N (rsubstSp Γ' ω N Sp (cutE N ωh))
  ... | Inr x' = ↓L pf⁻ ωh x' (rsubstSp Γ' ω N Sp (varE x' ωh))
  rsubstN Γ' ω N ⊥L ed = ⊥L
  rsubstN Γ' ω N (◇L N₁) ed = 
    ◇L λ ω' N₀ → rsubstN Γ' ω N (N₁ ω' (decut Γ' N N₀)) ·t
  rsubstN Γ' ω N (□L N₁) ed = 
    □L λ N₀ → rsubstN Γ' ω N (N₁ λ ω' → decut Γ' N (N₀ ω')) ·t
  rsubstN Γ' ω N (↑R V₁) ed = ↑R (rsubstV Γ' ω N V₁)
  rsubstN Γ' ω N (⊃R N₁) ed = ⊃R (rsubstN Γ' ω N N₁ I≡)

  rsubstSp Γ' ω N pL ed = pL
  rsubstSp Γ' ω N (↑L N₁) ed = ↑L (rsubstN Γ' ω N N₁ (atmE ed))
  rsubstSp Γ' ω N (⊃L V₁ Sp₂) ed with (evidenceA≺ ed) 
  ... | ≺*≡ = 
    ⊃L (rsubstV Γ' ω N V₁) 
      (rsubstSp Γ' ω N Sp₂ (appE ed (rsubstV Γ' ω N V₁)))
  ... | ≺*+ ωh'  =
    ⊃L (P.rsubstV (ih _ ωh') Γ' N V₁)
      (rsubstSp Γ' ω N Sp₂ (appE ed (P.rsubstV (ih _ ωh') Γ' N V₁)))

  lsubstN Γ' pf ω (L pf⁺ N₁) N' I≡ = 
    L pf⁺ (lsubstN (_ :: Γ') pf ω N₁
      (wkN <> (⊆to/wken (⊆to/refl _)) (I ω) N') ·f)
  lsubstN Γ' pf ≺*≡ (L pf⁺ N₁) N' (I+ ω' R) = 
    L pf⁺ (lsubstN (_ :: Γ') pf ≺*≡ N₁ 
      (edN {b = False} (N+ ω' R) I≡ N') ·f)
  lsubstN {w = w} Γ' pf (≺*+ ω) (L {wh = wh} pf⁺ N₁) N' (I+ ω' R) with dec≺ w wh 
  ... | Inl ω'' = {- 
    with dec≺ w wh
  lsubstN Γ' pf (≺*+ ω) (L pf⁺ N₁) N' (I+ ω' R) | Inl ≺*≡ =
    L pf⁺ (lsubstN (_ :: Γ') pf (≺*+ ω) N₁ 
      (edN (N+ ω' R) (I+ ω (Cut {!N₁!})) N') ·)
  lsubstN Γ' pf (≺*+ ω) (L pf⁺ N₁) N' (I+ ω' R) | Inl (≺*+ ω'') =
    L pf⁺ (lsubstN (_ :: Γ') pf (≺*+ ω) N₁ 
      (edN (N+ ω' R) (I+ ω (Cut {!N₁!})) N') ·)
  lsubstN Γ' pf (≺*+ ω) (L pf⁺ N₁) N' (I+ ω' R) | Inr ω'' = -}
    L pf⁺ (lsubstN (_ :: Γ') pf (≺*+ ω) N₁ 
      (edN (N+ ω' R) (I+ ω (Cut (unwind <> ω'' R (↑L (L pf⁺ N₁))))) N') ·f)
  ... | Inr ω'' = 
    L pf⁺ (lsubstN (_ :: Γ') pf (≺*+ ω) N₁ 
      (edN (N+ ω' R) (I+ ω (Cut (wkN <> (⊆to/stenirrev ω'' (⊆to/refl _)) · N₁))) N') ·f)

{-with ed
  ... | I≡ = L pf⁺ (lsubstN (_ :: Γ') pf ω N₁ 
    (wkN <> (⊆to/wken (⊆to/refl _)) (I ω) N') ·)
  ... | (I+ ω' R) with ω
  ... | ≺*≡ = L pf⁺ (lsubstN (_ :: Γ') pf ω N₁  
    
  ... | ≺*+ ω'' = L pf⁺ (lsubstN (_ :: Γ') pf ω N₁ 
    (edN (N+ ω' R) (I+ ω'' (Cut (edN {!!} {!!} N₁))) N') ·)
-}
--    L pf⁺ (lsubstN (_ :: Γ') pf ω N₁ (edN (N+ {!!} {!!}) (I+ {!!} (Cut {!N₁!})) N') ·)
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