-- KS4⁻ Sequent Calculus
-- A Constructive Logic of Provability
-- Robert J. Simmons, Bernardo Toninho

open import Compat
open import Accessibility.Inductive
import Accessibility.IndexedList as IndexedList

module CleanModal.Types (UWF : UpwardsWellFounded) where 

  open SuccStar UWF
  open IndexedList UWF

  Ctx : Set
  Ctx = List Type

  -- Contexts
  MCtx : Set
  MCtx = IList Type

  _atΓ_ : Ctx → W → MCtx
  Γ atΓ w = map (λ A → A at w) Γ
 
  ∈atΓ₁ : ∀{Γ x w} → x ∈ Γ → (x at w) ∈ (Γ atΓ w)
  ∈atΓ₁ i0 = i0
  ∈atΓ₁ (iS iN) = iS (∈atΓ₁ iN)

  ∈atΓ₂ : ∀{Γ x w} → (x at w) ∈ (Γ atΓ w) → x ∈ Γ 
  ∈atΓ₂ {[]} ()
  ∈atΓ₂ {_ ∷ Γ} i0 = i0
  ∈atΓ₂ {_ ∷ Γ} (iS iN) = iS (∈atΓ₂ iN)

  infix 10 _,_[_]
  _,_[_] : MCtx → Type → W → MCtx
  Δ , A [ w ] = (A at w) ∷ Δ

  -- Restriction
  _↓_ : MCtx → W → MCtx
  [] ↓ w = []
  ((A at w') ∷ Γ) ↓ w with w ≡? w'
  ((A at .w) ∷ Γ) ↓ w | inj₁ refl = Γ ↓ w
  ((A at w') ∷ Γ) ↓ w | inj₂ neq = (A at w') ∷ (Γ ↓ w)

  extend↓ : ∀{w A Γ} → ((Γ , A [ w ]) ↓ w) ≡ (Γ ↓ w)
  extend↓ {w} with w ≡? w
  ... | inj₁ refl = refl
  ... | inj₂ neq = abort (neq refl)

  ⊆at/↓ : (Γ : MCtx) {w : W} → (Γ ↓ w) ⊆ Γ at w
  ⊆at/↓ [] = λ()
  ⊆at/↓ ((A at wA) ∷ Γ) {w} with w ≡? wA
  ⊆at/↓ ((A at .w) ∷ Γ) {w} | inj₁ refl = ⊆at/wken (⊆at/↓ Γ)
  ⊆at/↓ ((A at wA) ∷ Γ) {w} | inj₂ neq = ⊆at/both (⊆at/↓ Γ)

  ⊆at/↓≺ : (Γ : MCtx) {w w' : W} → w ≺+ w' → Γ ⊆ (Γ ↓ w) at w'
  ⊆at/↓≺ [] ω = λ()
  ⊆at/↓≺ ((A at wA) ∷ Γ) {w} ω with w ≡? wA
  ⊆at/↓≺ ((A at .w) ∷ Γ) {w} ω | inj₁ refl = ⊆at/irrev (≺+⊀ ω) (⊆at/↓≺ Γ ω)
  ⊆at/↓≺ ((A at wA) ∷ Γ) {w} ω | inj₂ neq = ⊆at/both (⊆at/↓≺ Γ ω)

  ⊆to/↓ : (Γ : MCtx) {w : W} → (Γ ↓ w) ⊆ Γ to w
  ⊆to/↓ Γ = st (⊆at/↓ Γ) (λ ω → ⊆at/↓≺ Γ ω)

  ⊆to/↓≺ : (Γ : MCtx) {w w' : W} → w ≺+ w' → Γ ⊆ (Γ ↓ w) to w'
  ⊆to/↓≺ Γ ω = st (⊆at/↓≺ Γ ω) (λ ω' → ⊆at/≺+ (≺+trans ω ω') (⊆at/↓ Γ))

  -- Specific instances of generalized weakening
  exch/at : ∀{Γ w'' A w B w'} 
       → (Γ , A [ w ] , B [ w' ]) ⊆ (Γ , B [ w' ] , A [ w ]) at w''
  exch/at i0 = inj₁ (iS i0) 
  exch/at (iS i0) = inj₁ i0 
  exch/at {Γ}{w''} (iS (iS iN)) with ⊆at/refl {w''} Γ iN
  ... | inj₁ iN' = inj₁ (iS (iS iN'))
  ... | inj₂ ¬ω = inj₂ ¬ω 

  exch : ∀{Γ w'' A w B w'} 
       → (Γ , A [ w ] , B [ w' ]) ⊆ (Γ , B [ w' ] , A [ w ]) to w''
  exch = st exch/at (λ ω → exch/at)

  wken : ∀{Γ A w} → Γ ⊆ (Γ , A [ w ]) to w
  wken = ⊆to/wken (⊆to/refl _)

  wkex : ∀{Γ A w B w'} → (Γ , B [ w' ]) ⊆ (Γ , A [ w ] , B [ w' ]) to w
  wkex = ⊆to/both (⊆to/wken (⊆to/refl _))


