open import Compat
open import Accessibility.Inductive

module Accessibility.SuccStar (UWF : UpwardsWellFounded) where
  
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


  nrefl : (w w' : W) → w ≡ w' → w ≺ w' → Void
  nrefl w .w refl = ind (λ w → w ≺ w → Void) (λ w ih ω → ih w ω ω) w

  nrefl' : ∀{w w'} → w ≺ w' → w' ≡ w → Void
  nrefl' x y = nrefl _ _ (sym y) x

  nrefl+ : (w w' : W) → w ≡ w' → w ≺+ w' → Void
  nrefl+ w .w refl = ind+ (λ w → w ≺+ w → Void) (λ w ih ω → ih w ω ω) w

  nsym+ : (w w' : W) → w ≺+ w' → w' ≺+ w → Void
  nsym+ w w' ω ω' = nrefl+ w w refl (≺+trans ω ω')

  _⊀_ : W → W → Set
  w ⊀ w' = (w ≺+ w' → Void) × (w ≡ w' → Void)

  ⊀trans₂ : ∀{w₁ w₂ w₃} → w₁ ≺ w₂ → w₁ ⊀ w₃ → w₂ ≡ w₃ → Void
  ⊀trans₂ ω nω refl = proj₁ nω (≺+0 ω)

  ⊀trans : ∀{w₁ w₂ w₃} → w₁ ≺ w₂ → w₁ ⊀ w₃ → w₂ ⊀ w₃
  ⊀trans ω nω = (λ ω' → proj₁ nω (≺+S ω ω')) ^ ⊀trans₂ ω nω

  ≺⊀ : ∀{w w'} → w ≺ w' → w' ⊀ w
  ≺⊀ ω = (λ ω' → nsym+ _ _ (≺+0 ω) ω') ^ (λ eq' → nrefl _ _ (sym eq') ω)