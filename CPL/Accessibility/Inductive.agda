open import Prelude

module CPL.Accessibility.Inductive where

  record UpwardsWellFounded : Set1 where
    field
      W : Set
      _≺_ : W → W → Set
      _≡?_ : (w w' : W) → Decidable (w ≡ w')
      ind : (P : W → Set) 
              → ((w : W) → ((w' : W) → w ≺ w' → P w') → P w)
              → ((w : W) → P w)

  module SuccStar (UWF : UpwardsWellFounded) where
  
    open UpwardsWellFounded UWF public

    -- Transitive closure 
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

    -- Antireflexivity, antisymmetry
    nrefl : (w w' : W) → w ≡ w' → w ≺ w' → ⊥
    nrefl w .w Refl = ind (λ w → w ≺ w → ⊥) (λ w ih ω → ih w ω ω) w

    nrefl' : ∀{w w'} → w ≺ w' → w' ≡ w → ⊥
    nrefl' x y = nrefl _ _ (symm y) x

    nrefl+ : (w w' : W) → w ≡ w' → w ≺+ w' → ⊥
    nrefl+ w .w Refl = ind+ (λ w → w ≺+ w → ⊥) (λ w ih ω → ih w ω ω) w

    nsym+ : (w w' : W) → w ≺+ w' → w' ≺+ w → ⊥
    nsym+ w w' ω ω' = nrefl+ w w refl (≺+trans ω ω')

    -- Reflexive, transitive closure
    data _≺*_ : W → W → Set where
      ≺*≡ : ∀{w} → w ≺* w
      ≺*+ : ∀{w₁ w₂} → w₁ ≺+ w₂ → w₁ ≺* w₂

    -- Disconnectedness
    _⊀_ : W → W → Set
    w ⊀ w' = w ≺* w' → ⊥

    ⊀trans₂ : ∀{w₁ w₂ w₃} → w₁ ≺ w₂ → w₁ ⊀ w₃ → w₂ ≡ w₃ → ⊥
    ⊀trans₂ ω nω Refl = nω (≺*+ (≺+0 ω))

    ⊀trans : ∀{w₁ w₂ w₃} → w₁ ≺ w₂ → w₁ ⊀ w₃ → w₂ ⊀ w₃
    ⊀trans ω nω ≺*≡ = nω (≺*+ (≺+0 ω))
    ⊀trans ω nω (≺*+ ω') = nω (≺*+ (≺+S ω ω'))

    ≺⊀ : ∀{w w'} → w ≺ w' → w' ⊀ w
    ≺⊀ ω ≺*≡ = nrefl+ _ _ refl (≺+0 ω) 
    ≺⊀ ω (≺*+ ω') = nsym+ _ _ (≺+0 ω) ω'

    ≺+⊀ : ∀{w w'} → w ≺+ w' → w' ⊀ w
    ≺+⊀ ω ≺*≡ = nrefl+ _ _ refl ω
    ≺+⊀ ω (≺*+ ω') = nsym+ _ _ ω ω'

