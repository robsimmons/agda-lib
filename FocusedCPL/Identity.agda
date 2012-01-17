-- Constructive Provability Logic
-- Focused variant
-- Robert J. Simmons, Bernardo Toninho

-- Identity expansion

open import Prelude hiding (⊥)
open import Accessibility.Inductive
open import Accessibility.IndexedList
open import FocusedCPL.Core
open import FocusedCPL.Weakening
open import FocusedCPL.Atomic
open import FocusedCPL.Cut

module FocusedCPL.Identity where

module IDENTITY (UWF : UpwardsWellFounded)
  (dec≺ : (w w' : _) → Decidable (TRANS-UWF._≺*_ UWF w w')) where
  open TRANS-UWF UWF 
  open ILIST UWF
  open SEQUENT UWF
  open WEAKENING UWF
  open ATOMIC UWF
  open CUT UWF dec≺

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
    L pf⁺ (fsubN⁻ pf ·f (decutSp {b = False} (N+ ω pf⁺ R) E≡ Sp) N₁)
  fsubN⁻ pf ω Sp (↓L pf⁻ ωh x Sp') = 
    ↓L pf ωh x (fsubSp⁻ pf ωh (varE x ωh) Sp Sp')
  fsubN⁻ pf ω Sp ⊥L = ⊥L
  fsubN⁻ pf ω Sp (◇L N₁) = ◇L λ ω' N₀ → fsubN⁻ pf ·f Sp (N₁ ω' N₀)
  fsubN⁻ pf ω Sp (□L N₁) = □L λ N₀ → fsubN⁻ pf ·f Sp (N₁ λ ω' → N₀ ω')

  fsubSp⁻ pf ω ed Sp hyp⁻ = Sp
  fsubSp⁻ pf ω ed Sp (↑L N₁) = ↑L (fsubN⁻ pf (atmE ed) Sp N₁)
  fsubSp⁻ pf ω ed Sp (⊃L V₁ Sp₂) = ⊃L V₁ (fsubSp⁻ pf ω (appE ed V₁) Sp Sp₂)
  
  fsub⁻ : ∀{Γ A wc U}
    → U stable⁻
    → Spine [] Γ wc A wc U
    → Term [] Γ wc · (Abs A)
    → Term [] Γ wc · U
  fsub⁻ pf Sp N = fsubN⁻ pf ·f Sp N

  expand⁻ : ∀{A Γ wc} → Term [] Γ wc · (Abs A) → Term [] Γ wc · (Reg A)
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