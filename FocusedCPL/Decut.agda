-- Constructive Provability Logic
-- Focused variant
-- Robert J. Simmons, Bernardo Toninho

-- Removing an assumption given evidence

open import Prelude hiding (⊥)
open import Accessibility.Inductive
open import Accessibility.IndexedList
open import FocusedCPL.Core
open import FocusedCPL.IH
open import FocusedCPL.Evidence
open import FocusedCPL.Weakening

module FocusedCPL.Decut (UWF : UpwardsWellFounded) 
  (dec≺ : (w w' : _) → Decidable (TRANS-UWF._≺*_ UWF w w')) where

open TRANS-UWF UWF
open ILIST UWF
open SEQUENT UWF
open WEAKENING UWF
open EVIDENCE UWF dec≺
open IH UWF dec≺

module DECUT (wc : W) (ih : (wc' : W) → wc ≺+ wc' → P wc') where

  postulate XXX-HOLE : {A : Set} → String → A

  decutV : PdecutV wc
  decutN : PdecutN wc
  decutSp : PdecutSp wc

  decutV {Γ'} edΓ (pR x) = pR (LIST.SET.sub-append-congr Γ' LIST.SET.sub-wken x)
  decutV edΓ (↓R N₁) = ↓R (decutN edΓ ·t N₁)
  decutV edΓ (◇R ω N₁) = ◇R ω (P.decutN (ih _ (≺+0 ω)) (ed≺ ω edΓ) ·t N₁)
  decutV edΓ (□R N₁) = □R λ ω → P.decutN (ih _ (≺+0 ω)) (ed≺ ω edΓ) ·t (N₁ ω)

  decutN edΓ I≡ (L pf⁺ N₁) = L pf⁺ (decutN (C⊀ (nrefl+ _ _ refl) edΓ) ·t N₁)
  decutN edΓ (I+ ω R) (L pf⁺ N₁) = L pf⁺ (decutN (C+ ω R edΓ) ·t N₁)
  decutN {Γ'} edΓ ed (↓L pf⁻ ωh x Sp) = 
    ↓L pf⁻ ωh (LIST.SET.sub-append-congr Γ' LIST.SET.sub-wken x) 
      (decutSp edΓ (varE {b = True} x ωh) Sp)
  decutN edΓ ed ⊥L = ⊥L
  decutN edΓ ed (◇L N₁) = 
    ◇L λ ω N₀ → decutN edΓ ·t (N₁ ω (XXX-HOLE "I BELIEVE I CAN DO THIS"))
  decutN edΓ ed (□L N₁) = 
    □L λ N₀ → decutN edΓ ·t (N₁ λ ω → XXX-HOLE "I BELIEVE I CAN DO THIS")
  decutN edΓ ed (↑R V₁) = ↑R (decutV edΓ V₁)
  decutN edΓ ed (⊃R N₁) = ⊃R (decutN {b = True} edΓ I≡ N₁) 

  decutSp edΓ ed pL = pL
  decutSp edΓ ed (↑L N₁) = ↑L (decutN edΓ (atmE ed) N₁)
  decutSp edΓ E≡ (⊃L V₁ Sp₂) = 
    ⊃L (decutV edΓ V₁) (decutSp {b = True} edΓ (appE E≡ V₁) Sp₂)
  decutSp edΓ (E+ ω R) (⊃L V₁ Sp₂) = 
    ⊃L (P.decutV (ih _ ω) (ed≺+ ω edΓ) V₁) 
      (decutSp edΓ (appE (E+ ω R) V₁) Sp₂)

