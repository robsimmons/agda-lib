
open import Prelude hiding (⊥; [_])
open import Accessibility.Inductive
open import Accessibility.IndexedList
open import FocusedCPL.Core 
open import FocusedCPL.Weakening

module FocusedCPL.Evidence where

module EVIDENCE (UWF : UpwardsWellFounded) 
  (dec≺ : (w w' : _) → Decidable (TRANS-UWF._≺*_ UWF w w')) where

  open TRANS-UWF UWF
  open ILIST UWF
  open SEQUENT UWF
  open WEAKENING UWF

  data Atomic (א : FCtx) (Γ : MCtx) (wc : W) : Type ⁻ → Set where

    ↓E : ∀{A}
      (x : ↓ A at wc ∈ Γ)
      → Atomic א Γ wc A
    Cut : ∀{A} 
      (N : Term א Γ wc · (Reg A))
      → Atomic א Γ wc A
    ⊃E : ∀{A B}
      (R : Atomic א Γ wc (A ⊃ B))
      (V : Value א Γ wc A)
      → Atomic א Γ wc B


  data EvidenceA (Γ : MCtx) (wc : W) : Type ⁻ → W → Set where
    E≡ : ∀{A} → EvidenceA Γ wc A wc
    E+ : ∀{A w}
      (ω : wc ≺+ w) 
      (R : Atomic [] Γ w A)
      → EvidenceA Γ wc A w

  data EvidenceΩ (Γ : MCtx) (wc : W) : ICtx → Set where
    · : EvidenceΩ Γ wc ·
    I≡ : ∀{A} → EvidenceΩ Γ wc (I A wc)
    I+ : ∀{A w}
      (ω : wc ≺+ w) 
      (R : Atomic [] Γ w (↑ A))
      → EvidenceΩ Γ wc (I A w)

  postulate XXX-HOLE : {A : Set} → String → A

  varE : ∀{A Γ w wc} → (↓ A at w) ∈ Γ → wc ≺* w → EvidenceA Γ wc A w
  varE x ≺*≡ = E≡
  varE x (≺*+ ω) = E+ ω (↓E x)

  cutE : ∀{A Γ w wc} → Term [] Γ w · (Reg A) → wc ≺* w → EvidenceA Γ wc A w
  cutE N ≺*≡ = E≡
  cutE N (≺*+ ω) = E+ ω (Cut N)

  atmE : ∀{A Γ w wc} → EvidenceA Γ wc (↑ A) w → EvidenceΩ Γ wc (I A w)
  atmE E≡ = I≡
  atmE (E+ ω R) = I+ ω R 

  appE : ∀{A Γ w wc B} 
    → EvidenceA Γ wc (A ⊃ B) w 
    → Value [] Γ w A
    → EvidenceA Γ wc B w
  appE E≡ V = E≡
  appE (E+ ω R) V = E+ ω (⊃E R V)

  evidence≺ : ∀{w Γ Ω} 
    → EvidenceΩ Γ w Ω
    → w ≺' Ω 
  evidence≺ · = ·
  evidence≺ I≡ = I ≺*≡
  evidence≺ (I+ ω R) = I (≺*+ ω)

  ed-wkN₁ : ∀{w wh wc Γ C} {B : Type ⁺}
    → wc ≺* w
    → EvidenceΩ Γ wc (I B wh)
    → Term [] Γ w · (Reg C)
    → Term [] ((B at wh) :: Γ) w · (Reg C)
  ed-wkN₁ {w} {wh} ω ed N with dec≺ w wh 
  ed-wkN₁ ω ed N | Inr ωh =
    wkN <> (⊆to/wkenirrev ωh (⊆to/refl _)) · N
  ed-wkN₁ ω ed N | Inl ≺*≡ = 
    wkN <> (⊆to/wken (⊆to/refl _)) · N
  ed-wkN₁ ω I≡ N | Inl (≺*+ ωh) = abort (≺+⊀ ωh ω)
  ed-wkN₁ ω (I+ _ R) N | Inl (≺*+ ωh) = XXX-HOLE "WHOO" -- XXX-HOLE "WHOO"

  ed-wkN₂ : ∀{w wh wc Γ B C} {A : Type ⁺}
    → wc ≺* w
    → EvidenceΩ Γ wc (I B wh)
    → Term [] Γ wc (I A w) (Reg C)
    → Term [] ((B at wh) :: Γ) wc (I A w) (Reg C)
  ed-wkN₂ ω I≡ N = wkN <> (⊆to/wken (⊆to/refl _)) (I ω) N
  ed-wkN₂ {w} {wh} ω (I+ ω' R) N with dec≺ w wh
  ed-wkN₂ ω (I+ ω' R) N | Inr ωh = XXX-HOLE "WHOO"
  ed-wkN₂ ω (I+ ω' R) N | Inl ωh = XXX-HOLE "WHOO"

  
--  Evidence Γ :
{-
  edN : 
    → (Γ' : Ctx)
    → 
-}

{-
with dec≺ w wh 
  ed-wkN₂ ω ed ed' N | Inr ωh =
    wkN <> (⊆to/wkenirrev ωh (⊆to/refl _)) (evidence≺ ed') N
  ed-wkN₂ ω ed ed' N | Inl ≺*≡ = 
    wkN <> (⊆to/wken (⊆to/refl _)) (evidence≺ ed') N
  ed-wkN₂ ω I≡ ed' N | Inl (≺*+ ωh) = abort (≺+⊀ ωh ω)
  ed-wkN₂ ω (I+ _ R) ed' N | Inl (≺*+ ωh) = XXX-HOLE "WHOO" -- XXX-HOLE "WHOO"
-}
  -- Note - we can now prove this after cut.

{-
  ed-wkN+ : ∀{Γ Ω wc w A C} (Γ' : MCtx)
    → wc ≺+ w
    → Atomic [] Γ w (↑ A)
    → Term [] (Γ' ++ Γ) wc Ω (Reg C)
    → wc ≺' Ω
    → Term [] (Γ' ++ (A at w) :: Γ) wc Ω (Reg C)  

  ed-wkN+ ω R N = {!N!}

  ed-wkN : ∀{Γ Ω wc w A C} (Γ' : MCtx)
    → EvidenceΩ Γ wc (I A w)
    → Term [] (Γ' ++ Γ) wc Ω (Reg C)
    → wc ≺' Ω
    → Term [] (Γ' ++ (A at w) :: Γ) wc Ω (Reg C)  
  ed-wkN Γ' I≡ N ed =
    wkN <> (⊆to/append-congr Γ' (⊆to/wken (⊆to/refl _))) ed N
  ed-wkN Γ' (I+ ω R) N ed = {!!}
-}