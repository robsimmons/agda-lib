
open import Prelude hiding (⊥)
open import Accessibility.Inductive
open import Accessibility.IndexedList
open import FocusedCPL.Core 
open import FocusedCPL.Weakening

module FocusedCPL.Cut.Evidence (UWF : UpwardsWellFounded) where
open TRANS-UWF UWF

module EVIDENCE (dec≺ : (w w' : _) → Decidable (w ≺* w')) where
  open ILIST UWF
  open SEQUENT UWF
  open WEAKENING UWF

  data Atomic (א : FCtx) (Γ : MCtx) (wc : W) : Type ⁻ → Bool → Set where
    ↓E : ∀{A b}
      (x : ↓ A at wc ∈ Γ)
      → Atomic א Γ wc A b
    Cut : ∀{A} 
      (N : Term א Γ wc · (Reg A)) 
      → Atomic א Γ wc A True
    ⊃E : ∀{A B b}
      (R : Atomic א Γ wc (A ⊃ B) b)
      (V : Value א Γ wc A)
      → Atomic א Γ wc B b

  -- The boolean flag is a graceless mechanism, but the point is that, if you 
  -- commit yourself to not using cut, there's a trivial "unwind" 

  unwind : ∀{א Γ A U w wc}
    → U stable⁻
    → wc ≺* w
    → Atomic א Γ w A False
    → Spine א Γ w A wc U
    → Term א Γ wc · U
  unwind pf ω (↓E x) Sp = ↓L pf ω x Sp
  unwind pf ω (⊃E R V) Sp = unwind pf ω R (⊃L V Sp) 

  subset : ∀{א Γ w A b}
    → Atomic א Γ w A b
    → Atomic א Γ w A True
  subset (↓E x) = ↓E x
  subset (Cut N) = Cut N
  subset (⊃E R V) = ⊃E (subset R) V

  wkR : ∀{א Γ Γ' wc A b}
    → Γ ⊆ Γ' to wc
    → Atomic א Γ wc A b
    → Atomic א Γ' wc A b
  wkR θ (↓E x) = ↓E (⊆to/now θ x)
  wkR θ (Cut N) = Cut (wkN <> θ · N)
  wkR θ (⊃E R V) = ⊃E (wkR θ R) (wkV <> θ V)

  data EvidenceA (Γ : MCtx) (wc : W) : Type ⁻ → W → Bool → Set where
    E≡ : ∀{A b} → EvidenceA Γ wc A wc b
    E+ : ∀{A w b}
      (ω : wc ≺+ w) 
      (R : Atomic [] Γ w A b)
      → EvidenceA Γ wc A w b

  data EvidenceΩ (Γ : MCtx) (wc : W) : ICtx → Bool → Set where
    ·t : EvidenceΩ Γ wc · True
    ·f : EvidenceΩ Γ wc · False
    I≡ : ∀{A b} → EvidenceΩ Γ wc (I A wc) b
    I+ : ∀{A w b}
      (ω : wc ≺+ w) 
      (R : Atomic [] Γ w (↑ A) b)
      → EvidenceΩ Γ wc (I A w) b

  varE : ∀{A Γ w wc b} → (↓ A at w) ∈ Γ → wc ≺* w → EvidenceA Γ wc A w b
  varE x ≺*≡ = E≡
  varE x (≺*+ ω) = E+ ω (↓E x)

  cutE : ∀{A Γ w wc} → Term [] Γ w · (Reg A) → wc ≺* w 
    → EvidenceA Γ wc A w True
  cutE N ≺*≡ = E≡
  cutE N (≺*+ ω) = E+ ω (Cut N)

  atmE : ∀{A Γ w wc b} → EvidenceA Γ wc (↑ A) w b → EvidenceΩ Γ wc (I A w) b
  atmE E≡ = I≡
  atmE (E+ ω R) = I+ ω R 

  appE : ∀{A Γ w wc B b} 
    → EvidenceA Γ wc (A ⊃ B) w b
    → Value [] Γ w A
    → EvidenceA Γ wc B w b
  appE E≡ V = E≡
  appE (E+ ω R) V = E+ ω (⊃E R V)

  evidenceΩ≺ : ∀{w Γ Ω b} 
    → EvidenceΩ Γ w Ω b
    → w ≺' Ω 
  evidenceΩ≺ ·t = ·
  evidenceΩ≺ ·f = ·
  evidenceΩ≺ I≡ = I ≺*≡
  evidenceΩ≺ (I+ ω R) = I (≺*+ ω)

  evidenceA≺ : ∀{w w' Γ A b}
    → EvidenceA Γ w A w' b
    → w ≺* w'
  evidenceA≺ E≡ = ≺*≡
  evidenceA≺ (E+ ω R) = ≺*+ ω


  data Evidence (Γ : MCtx) (wc : W) : MCtx → Item (Type ⁺) → Set where
    N⊀ : ∀{w A} → 
      (ω : wc ≺+ w → Void)
      → Evidence Γ wc [] (A at w)      
    N+ : ∀{w A b} → 
      (ω : wc ≺+ w)
      (pf⁺ : A stable⁺)
      (R : Atomic [] Γ w (↑ A) b)
      → Evidence Γ wc [] (A at w)
    C⊀ : ∀{w A Γ' Item}
      (ω : wc ≺+ w → Void)
      (edΓ : Evidence Γ wc Γ' Item) 
      → Evidence Γ wc ((A at w) :: Γ') Item
    C+ : ∀{w A Γ' Item b}
      (ω : wc ≺+ w)
      (pf⁺ : A stable⁺)
      (R : Atomic [] (Γ' ++ Γ) w (↑ A) b)
      (edΓ : Evidence Γ wc Γ' Item) 
      → Evidence Γ wc ((A at w) :: Γ') Item

  ed-stable : ∀{Γ w Γ' A w'}
    → w ≺+ w'
    → Evidence Γ w Γ' (A at w')
    → A stable⁺
  ed-stable ω (N⊀ ω') = abort (ω' ω)
  ed-stable ω (N+ ω' pf⁺ R) = pf⁺
  ed-stable ω (C⊀ ω' edΓ) = ed-stable ω edΓ
  ed-stable ω (C+ ω' pf⁺ R edΓ) = ed-stable ω edΓ
 
  ed≺ : ∀{w w' Γ Γ' Item} 
    → w ≺ w'
    → Evidence Γ w Γ' Item 
    → Evidence Γ w' Γ' Item
  ed≺ ω (N⊀ ω') = N⊀ (ω' o ≺+S ω)
  ed≺ {w} {w'} ω (N+ {wn} _ pf⁺ R) with dec≺ w' wn
  ed≺ ω (N+ _ _ R) | Inl ≺*≡ = N⊀ (nrefl+ _ _ refl)
  ... | Inl (≺*+ ω') = N+ ω' pf⁺ R
  ... | Inr ω' = N⊀ (ω' o ≺*+)
  ed≺ ω (C⊀ ω' edΓ) = C⊀ (ω' o ≺+S ω) (ed≺ ω edΓ)
  ed≺ {w} {w'} ω (C+ {wn} _ pf⁺ R edΓ) with dec≺ w' wn
  ed≺ ω (C+ ω' _ R edΓ) | Inl ≺*≡ = C⊀ (nrefl+ _ _ refl) (ed≺ ω edΓ)
  ... | Inl (≺*+ ω') = C+ ω' pf⁺ R (ed≺ ω edΓ)
  ... | Inr ω' = C⊀ (ω' o ≺*+) (ed≺ ω edΓ)

  ed≺+ : ∀{w w' Γ Γ' Item} 
    → w ≺+ w'
    → Evidence Γ w Γ' Item 
    → Evidence Γ w' Γ' Item
  ed≺+ (≺+0 ω) edΓ = ed≺ ω edΓ
  ed≺+ (≺+S ω ω') edΓ = ed≺+ ω' (ed≺ ω edΓ) 

  ed≺* : ∀{w w' Γ Γ' Item} 
    → w ≺* w'
    → Evidence Γ w Γ' Item 
    → Evidence Γ w' Γ' Item
  ed≺* ≺*≡ edΓ = edΓ
  ed≺* (≺*+ ω) edΓ = ed≺+ ω edΓ



{-
  sub-append-swap₂ : {A : Set} → ∀{zs y} 
    (xs : List A)
    → LIST.SET.Sub (xs ++ (y :: zs)) (y :: (xs ++ zs))
  sub-append-swap₁ [] ys n = n
  sub-append-swap₁ xs [] n = n
  sub-append-swap₁ xs (x :: ys) n = 
    S (sub-append-swap₁ xs ys {!!}) -}

{-
  deN : ∀{Γ A w wc C}
    → EvidenceΩ Γ wc (I A w)
    → Term [] ((A at w) :: Γ) wc · C
    → Term [] Γ wc · C
  deN I≡ N = {!!}
  deN (I+ ω R) N = {!!}
-}




{-
with dec≺ w wh
  ed-wkN₂ ω (I+ ω' R) N | Inr ωh =  "WHOO"
  ed-wkN₂ ω (I+ ω' R) N | Inl ωh =  "WHOO" -}

  
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
  ed-wkN₂ ω (I+ _ R) ed' N | Inl (≺*+ ωh) = 
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