-- Constructive Provability Logic
-- Focused variant
-- Robert J. Simmons, Bernardo Toninho

-- Identity expansion

open import Prelude hiding (⊥; [_])
open import Accessibility.Inductive
open import Accessibility.IndexedList
open import FocusedCPL.Core
open import FocusedCPL.Weakening
open import FocusedCPL.Cut

module FocusedCPL.Identity where

module IDENTITY (UWF : UpwardsWellFounded) where
  open TRANS-UWF UWF 
  open ILIST UWF
  open SEQUENT UWF
  open WEAKENING UWF
  open CUT UWF

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

  unwind : ∀{א Γ A U w wc}
    → U stable⁻
    → wc ≺* w
    → Atomic א Γ w A False
    → Spine א Γ w A wc U
    → Term א Γ wc · U
  unwind pf ω (↓E x) Sp = ↓L pf ω x Sp
  unwind pf ω (⊃E R V) Sp = unwind pf ω R (⊃L V Sp) 

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

  atmE : ∀{A Γ w wc b} → EvidenceA Γ wc (↑ A) w b → EvidenceΩ Γ wc (I A w) b
  atmE E≡ = I≡
  atmE (E+ ω R) = I+ ω R 

  appE : ∀{A Γ w wc B b} 
    → EvidenceA Γ wc (A ⊃ B) w b
    → Value [] Γ w A
    → EvidenceA Γ wc B w b
  appE E≡ V = E≡
  appE (E+ ω R) V = E+ ω (⊃E R V)

{-
  unwind* : ∀{א Γ A U w wc}
    → U stable⁻
    → wc ≺* w
    → Atomic א Γ w A False
    → Spine א Γ w A wc U
    → Term א Γ wc · U
  unwind* pf ω (↓E x) Sp = ↓L pf ω x Sp
  unwind* pf ω (⊃E R V) Sp = unwind pf ω R (⊃L V Sp) 

  unwindN : ∀{Γ A U w wc Ω}
    → U stable⁻
    → wc ≺* w
    → Atomic [] Γ w (↑ A) False
    → Term [] ((A at w) :: Γ) wc Ω U
    → Term [] Γ wc Ω U
  unwindN pf ω R (L pf⁺ N₁) = {!!}
  unwindN pf ω R (↓L pf⁻ ωh x Sp) = {!!}
  unwindN pf ω R ⊥L = {!!}
  unwindN pf ω R (◇L N₁) = {!◇L!}
  unwindN pf ω R (□L N₁) = {!!}
  unwindN pf ω R (↑R V₁) = {!!}
  unwindN () ω R (⊃R N₁) 

  unwindSp : ∀{Γ A U w wc B wb}
    → U stable⁻
    → wc ≺* w
    → Atomic [] Γ w (↑ A) False
    → Spine [] ((A at w) :: Γ) wb B wc U
    → Spine [] Γ wb B wc U
  unwindSp pf ω R hyp⁻ = hyp⁻
  unwindSp pf ω R pL = pL
  unwindSp pf ω R (↑L N₁) = ↑L {!unwindN!}
  unwindSp pf ω R (⊃L V₁ Sp₂) = {!!}
-}

  fsubN⁻ : ∀{Γ A wc Ω U}
    → U stable⁻
    → EvidenceΩ Γ wc Ω False
    → Spine [] Γ wc A wc U
    → Term [] Γ wc Ω (Abs A)
    → Term [] Γ wc Ω U

  fsubSp⁻ : ∀{Γ A wc wh B U}
    → U stable⁻
    → wc ≺* wh
    → EvidenceA Γ wc B wh False
    → Spine [] Γ wc A wc U
    → Spine [] Γ wh B wc (Abs A)
    → Spine [] Γ wh B wc U

  fsubN⁻ pf I≡ Sp (L pf⁺ N₁) = 
    L pf⁺ (fsubN⁻ pf ·f (wkSp <> (⊆to/wken (⊆to/refl _)) ≺*≡ Sp) N₁)
  fsubN⁻ pf (I+ ω R) Sp (L pf⁺ N₁) = 
    L pf⁺ (fsubN⁻ pf ·f {!!} N₁)
  fsubN⁻ pf ω Sp (↓L pf⁻ ωh x Sp') = ↓L pf ωh x (fsubSp⁻ pf ωh (varE x ωh) Sp Sp')
  fsubN⁻ pf ω Sp ⊥L = ⊥L
  fsubN⁻ pf ω Sp (◇L N₁) = ◇L λ ω' N₀ → fsubN⁻ pf ·f Sp (N₁ ω' N₀)
  fsubN⁻ pf ω Sp (□L N₁) = □L λ N₀ → fsubN⁻ pf ·f Sp (N₁ λ ω' → N₀ ω')

  fsubSp⁻ pf ω ed Sp hyp⁻ = Sp
  fsubSp⁻ pf ω ed Sp (↑L N₁) = ↑L (fsubN⁻ pf (atmE ed) Sp N₁)
  fsubSp⁻ pf ω ed Sp (⊃L V₁ Sp₂) = ⊃L V₁ (fsubSp⁻ pf ω (appE ed V₁) Sp Sp₂)

  
  fsub⁻ : ∀{א Γ A wc U}
    → U stable⁻
    → Spine א Γ wc A wc U
    → Term א Γ wc · (Abs A)
    → Term א Γ wc · U

  fsub⁻ = {!!}

  expand⁻ : ∀{A א Γ wc} → Term א Γ wc · (Abs A) → Term א Γ wc · (Reg A)
  expand⁻ {a Q .⁻} N = fsub⁻ <> pL N
  expand⁻ {↑ (a Q .⁺)} N = 
    fsub⁻ <> (↑L (L <> (↑R (pR Z)))) N
  expand⁻ {↑ (↓ A)} N = 
    fsub⁻ <> (↑L (L <> (↑R (↓R (expand⁻ {A} (↓L <> ≺*≡ Z hyp⁻)))))) N
  expand⁻ {↑ ⊥} N = 
    fsub⁻ <> (↑L ⊥L) N
  expand⁻ {↑ (◇ A)} N = 
    fsub⁻ <> (↑L (◇L λ ω N₀ → ↑R (◇R ω N₀))) N
  expand⁻ {↑ (□ A)} N = 
    fsub⁻ <> (↑L (□L λ N₀ → ↑R (□R λ ω → N₀ ω))) N
  expand⁻ {a Q .⁺ ⊃ B} N = 
    ⊃R (L <> (expand⁻ (fsub⁻ <> (⊃L (pR Z) hyp⁻) 
                        (wkN <> (⊆to/wken (⊆to/refl _)) · N))))
  expand⁻ {↓ A ⊃ B} N = 
    ⊃R (L <> (expand⁻ (fsub⁻ <> (⊃L (↓R (expand⁻ (↓L <> ≺*≡ Z hyp⁻))) hyp⁻) 
                        (wkN <> (⊆to/wken (⊆to/refl _)) · N))))
  expand⁻ {⊥ ⊃ B} N = 
    ⊃R ⊥L
  expand⁻ {◇ A ⊃ B} N = 
    ⊃R (◇L λ ω N₀ → expand⁻ (fsub⁻ <> (⊃L (◇R ω N₀) hyp⁻) N))
  expand⁻ {□ A ⊃ B} N = 
    ⊃R (□L (λ N₀ → expand⁻ (fsub⁻ <> (⊃L (□R (λ ω → N₀ ω)) hyp⁻) N)))