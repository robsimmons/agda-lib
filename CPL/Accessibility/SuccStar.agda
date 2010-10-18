open import Prelude
open import CPL.Accessibility.Inductive

module CPL.Accessibility.SuccStar (UWF : UpwardsWellFounded) where
  
  open UpwardsWellFounded UWF public

  data _≺+_ : W → W → Set where
    ≺+0 : ∀{w₁ w₂} → w₁ ≺ w₂ → w₁ ≺+ w₂
    ≺+S : ∀{w₁ w₂ w₃} → w₁ ≺ w₂ → w₂ ≺+ w₃ → w₁ ≺+ w₃

  ≺+S' : ∀{w₁ w₂ w₃} → w₁ ≺+ w₂ → w₂ ≺ w₃ → w₁ ≺+ w₃
  ≺+S' (≺+0 ω₁) ω = ≺+S ω₁ (≺+0 ω)
  ≺+S' (≺+S ω₁ ω+) ω = ≺+S ω₁ (≺+S' ω+ ω)

  ≺+trans : ∀{w₁ w₂ w₃} → w₁ ≺+ w₂ → w₂ ≺+ w₃ → w₁ ≺+ w₃
  ≺+trans (≺+0 ω₁) ω = ≺+S ω₁ ω
  ≺+trans (≺+S ω₁ ω+) ω = ≺+S ω₁ (≺+trans ω+ ω)

  ind+P : (W → Set) → W → Set
  ind+P = λ P w → ((w' : W) → w ≺+ w' → P w')

  ind+₁ : (P : W → Set) 
           → ((w : W) → ((w' : W) → w ≺+ w' → P w') → P w)
           → ((w : W) → ((w' : W) → w ≺ w' → ind+P P w') → ind+P P w)
  ind+₁ P f w iH w' (≺+0 ω) = f w' (iH w' ω)
  ind+₁ P f w iH w' (≺+S ω sN) = iH _ ω w' sN

  ind+₂ : (P : W → Set) 
           → ((w : W) → ((w' : W) → w ≺+ w' → P w') → P w)
           → (w : W) → ind+P P w
  ind+₂ P f w = ind (λ w → ind+P P w) (ind+₁ P f) w

  ind+ : (P : W → Set) 
           → ((w : W) → ((w' : W) → w ≺+ w' → P w') → P w)
           → (w : W) → P w
  ind+ P f w = f w (ind+₂ P f w) 


  nrefl : (w w' : W) → w ≡ w' → w ≺ w' → ⊥
  nrefl w .w Refl = ind (λ w → w ≺ w → ⊥) (λ w ih ω → ih w ω ω) w

  nrefl' : ∀{w w'} → w ≺ w' → w' ≡ w → ⊥
  nrefl' x y = nrefl _ _ (symm y) x

  nrefl+ : (w w' : W) → w ≡ w' → w ≺+ w' → ⊥
  nrefl+ w .w Refl = ind+ (λ w → w ≺+ w → ⊥) (λ w ih ω → ih w ω ω) w

  nsym+ : (w w' : W) → w ≺+ w' → w' ≺+ w → ⊥
  nsym+ w w' ω ω' = nrefl+ w w refl (≺+trans ω ω')

  _⊀_ : W → W → Set
  w ⊀ w' = (w ≺+ w' → ⊥) × (w ≡ w' → ⊥)

  ⊀trans₂ : ∀{w₁ w₂ w₃} → w₁ ≺ w₂ → w₁ ⊀ w₃ → w₂ ≡ w₃ → ⊥
  ⊀trans₂ ω nω Refl = fst nω (≺+0 ω)

  ⊀trans : ∀{w₁ w₂ w₃} → w₁ ≺ w₂ → w₁ ⊀ w₃ → w₂ ⊀ w₃
  ⊀trans ω nω = (λ ω' → fst nω (≺+S ω ω')) , ⊀trans₂ ω nω

  ≺⊀ : ∀{w w'} → w ≺ w' → w' ⊀ w
  ≺⊀ ω = (λ ω' → nsym+ _ _ (≺+0 ω) ω') , (λ eq' → nrefl _ _ (symm eq') ω)