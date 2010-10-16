-- K4W⁻ Natural Deduction
-- A Constructive Logic of Provability
-- Robert J. Simmons, Bernardo Toninho

open import Compat
open import Accessibility.Inductive 
import Accessibility.IndexedList as IndexedList 
import Basic.Core as Core 

module Basic.NatDeduction (UWF : UpwardsWellFounded) where

  open SuccStar UWF
  open IndexedList UWF
  open Core UWF 

  {- Weakening (outside the metric) -}

  wkP : W → Set
  wkP = λ w → ∀{Γ Γ' A} → Γ ⊆ Γ' to w → Γ ⊢ A [ w ] → Γ' ⊢ A [ w ]
  
  wk₁ : (w : W) → ((w' : W) → w ≺ w' → wkP w') → wkP w
  wk₁ w ih sub (hyp iN) = hyp (⊆to/now sub iN)
  wk₁ w ih sub (⊃I D) = ⊃I (wk₁ w ih (⊆to/both sub) D)
  wk₁ w ih sub (⊃E D₁ D₂) = ⊃E (wk₁ w ih sub D₁) (wk₁ w ih sub D₂)
  wk₁ w ih sub (□I D) = □I (λ ω → ih _ ω (⊆to/≺ (≺+0 ω) sub) (D ω))
  wk₁ w ih sub (□E D₁ D₂) = □E (wk₁ w ih sub D₁) 
    (λ D₀ → wk₁ w ih sub (D₂ (λ ω → ih _ ω (⊆to/≺' (≺+0 ω) sub) (D₀ ω))))
  wk₁ w ih sub (◇I ω D) = ◇I ω (ih _ ω (⊆to/≺ (≺+0 ω) sub) D)
  wk₁ w ih sub (◇E D D') = ◇E (wk₁ w ih sub D) 
    (λ ω D₀ → wk₁ w ih sub (D' ω (ih _ ω (⊆to/≺' (≺+0 ω) sub) D₀)))
  wk₁ w ih sub (¬□I D) 
   = ¬□I (λ ω D₀ → D ω (ih _ ω (⊆to/≺' (≺+0 ω) sub) D₀))
  wk₁ w ih sub (¬□E D₁ D₂)
   = ¬□E (wk₁ w ih sub D₁) 
    (λ D₀ → wk₁ w ih sub (D₂ (λ ω D → D₀ ω (ih _ ω (⊆to/≺ (≺+0 ω) sub) D))))
  wk₁ w ih sub (¬◇I ω D) = ¬◇I ω (λ D₀ → D (ih _ ω (⊆to/≺' (≺+0 ω) sub) D₀))
  wk₁ w ih sub (¬◇E D₁ D₂) 
   = ¬◇E (wk₁ w ih sub D₁) 
     (λ ω D₀ → wk₁ w ih sub 
      (D₂ ω (λ D → D₀ (ih _ ω (⊆to/≺ (≺+0 ω) sub) D))))

  wk : ∀{Γ Γ' w A}
       → Γ ⊆ Γ' to w
       → Γ ⊢ A [ w ] 
       → Γ' ⊢ A [ w ]
  wk = ind wkP wk₁ _

 
  {- Metric -}

  data ND : (w : W) (Γ Δ : MCtx) → Shape Δ w → Type → Set where
    hyp' : ∀{w A Γ Δ} 
      → A at w ∈ Γ
      → ND w Γ Δ s0 (A)
    ⊃I' : ∀{w A B Γ Δ s}
      → ND w (Γ , A [ w ]) Δ s B
      → ND w Γ Δ (s1 s) (A ⊃ B)
    ⊃E' : ∀{B w A Γ Δ s₁ s₂}
      → ND w Γ Δ s₁ (A ⊃ B) 
      → ND w Γ Δ s₂ A
      → ND w Γ Δ (s2 s₁ s₂) B
    □I' : ∀{w A Γ Δ}
      → (∀{w'} → w ≺ w' → Δ ⊢ A [ w' ]) 
      → ND w Γ Δ s0 (□ A) 
    □E' : ∀{w A Γ Δ C s₀}
      → ND w Γ Δ s₀ (□ A)
      → (s : (∀{w'} → w ≺ w' → Δ ⊢ A [ w' ]) → Shape Δ w)
      → ((D₀ : ∀{w'} → w ≺ w' → Δ ⊢ A [ w' ]) → ND w Γ Δ (s D₀) C)
      → ND w Γ Δ (s2 s₀ (s□⊢ s)) C
    ◇I' : ∀{Γ Δ A w w'}
      → w ≺ w'
      → Δ ⊢ A [ w' ]
      → ND w Γ Δ s0 (◇ A)
    ◇E' : ∀{Γ Δ A C w s₀}
      → ND w Γ Δ s₀ (◇ A)
      → (s : ∀{w'} → w ≺ w' → Δ ⊢ A [ w' ] → Shape Δ w)
      → (∀{w'} (ω : w ≺ w') (D₀ : Δ ⊢ A [ w' ]) → ND w Γ Δ (s ω D₀) C)
      → ND w Γ Δ (s2 s₀ (s◇⊢ s)) C
    ¬□I' : ∀{w A Γ Δ}
      → (∀{w'} → w ≺ w' → Δ ⊢ A [ w' ] → Void) 
      → ND w Γ Δ s0 (¬□ A) 
    ¬□E' : ∀{w A Γ Δ C s₀}
      → ND w Γ Δ s₀ (¬□ A)
      → (s : (∀{w'} → w ≺ w' → Δ ⊢ A [ w' ] → Void) → Shape Δ w)
      → ((D₀ : ∀{w'} → w ≺ w' → Δ ⊢ A [ w' ] → Void) → ND w Γ Δ (s D₀) C)
      → ND w Γ Δ (s2 s₀ (s¬□⊢ s)) C
    ¬◇I' : ∀{Γ Δ A w w'}
      → w ≺ w'
      → (Δ ⊢ A [ w' ] → Void)
      → ND w Γ Δ s0 (¬◇ A)
    ¬◇E' : ∀{Γ Δ A C w s₀}
      → ND w Γ Δ s₀ (¬◇ A)
      → (s : ∀{w'} → w ≺ w' → (Δ ⊢ A [ w' ] → Void) → Shape Δ w)
      → (∀{w'} (ω : w ≺ w') (D₀ : Δ ⊢ A [ w' ] → Void) → ND w Γ Δ (s ω D₀) C)
      → ND w Γ Δ (s2 s₀ (s¬◇⊢ s)) C


  -- Getting in and out of the metric
  m→ : ∀{Γ Δ w A s} → Δ ⊆ Γ to w → ND w Γ Δ s A → Γ ⊢ A [ w ]
  m→ sub (hyp' iN) = hyp iN
  m→ sub (⊃I' D) = ⊃I (m→ (⊆to/wken sub) D)
  m→ sub (⊃E' DA D) = ⊃E (m→ sub DA) (m→ sub D)
  m→ sub (□I' D) = □I (λ ω → wk (⊆to/≺ (≺+0 ω) sub) (D ω) )
  m→ sub (□E' DA s D) 
   = □E (m→ sub DA) (λ D₀ → m→ sub (D (λ ω → wk (⊆to/≺' (≺+0 ω) sub) (D₀ ω))))
  m→ sub (◇I' ω D) = ◇I ω (wk (⊆to/≺ (≺+0 ω) sub) D)
  m→ sub (◇E' DA s D) 
   = ◇E (m→ sub DA) (λ ω D₀ → m→ sub (D ω (wk (⊆to/≺' (≺+0 ω) sub) D₀)))
  m→ sub (¬□I' D) = ¬□I (λ ω D₀ → D ω (wk (⊆to/≺' (≺+0 ω) sub) D₀))
  m→ sub (¬□E' DA s D) 
   = ¬□E (m→ sub DA) 
       (λ D₀ → m→ sub (D (λ ω D' → D₀ ω (wk (⊆to/≺ (≺+0 ω) sub) D'))))
  m→ sub (¬◇I' ω D) = ¬◇I ω (λ D₀ → D (wk (⊆to/≺' (≺+0 ω) sub) D₀))
  m→ sub (¬◇E' DA s D) 
   = ¬◇E (m→ sub DA) 
       (λ ω D₀ → m→ sub (D ω (λ D' → D₀ (wk (⊆to/≺ (≺+0 ω) sub) D'))))

  →m : ∀{Γ w Δ A} → (Γ ↓ w) ≡ Δ → Γ ⊢ A [ w ] → Σ λ s → ND w Γ Δ s A
  →m refl (hyp iN) = ^ hyp' iN
  →m {Γ} refl (⊃I D) = ^ ⊃I' (proj₂ (→m extend↓ D))
  →m refl (⊃E D₁ D₂)
   = ^ (⊃E' (proj₂ (→m refl D₁)) (proj₂ (→m refl D₂)) )
  →m {Γ} refl (□I D) = ^ □I' (λ ω → wk (⊆to/↓≺ Γ (≺+0 ω)) (D ω))
  →m {Γ} refl (□E D₁ D₂) 
   = ^ (□E' (proj₂ (→m refl D₁)) _
    (λ D₀ → proj₂ (→m refl (D₂ (λ ω → wk (⊆to/≺ (≺+0 ω) (⊆to/↓ Γ)) (D₀ ω))))))
  →m refl (◇I ω D) = ^ ◇I' ω (wk (⊆to/↓≺ _ (≺+0 ω)) D)
  →m refl (◇E D₁ D₂) 
   = ^ ◇E' (proj₂ (→m refl D₁)) _ 
    (λ ω D₀ → proj₂ (→m refl (D₂ ω (wk (⊆to/≺ (≺+0 ω) (⊆to/↓ _)) D₀))))
  →m refl (¬□I D) 
   = ^ ¬□I' (λ ω D₀ → D ω (wk (⊆to/≺ (≺+0 ω) (⊆to/↓ _)) D₀))
  →m refl (¬□E D₁ D₂) 
   = ^ ¬□E' (proj₂ (→m refl D₁)) _ 
    (λ D₀ → proj₂ 
      (→m refl (D₂ (λ ω D' → D₀ ω (wk (⊆to/↓≺ _ (≺+0 ω)) D')))))
  →m refl (¬◇I ω D) 
   = ^ ¬◇I' ω (λ D₀ → D (wk (⊆to/≺ (≺+0 ω) (⊆to/↓ _)) D₀))
  →m refl (¬◇E D₁ D₂) 
   = ^ ¬◇E' (proj₂ (→m refl D₁)) _ 
    (λ ω D₀ → proj₂ 
      (→m refl (D₂ ω (λ D' → D₀ (wk (⊆to/↓≺ _ (≺+0 ω)) D')))))


  {- Weakening (inside the metric) -}

  wk' : ∀{Γ Γ' w Δ s A}
       → Γ ⊆ Γ' to w
       → ND w Γ Δ s A 
       → ND w Γ' Δ s A
  wk' sub (hyp' iN) = hyp' (⊆to/now sub iN)
  wk' sub (⊃I' D) = ⊃I' (wk' (⊆to/both sub) D)
  wk' sub (⊃E' D₁ D₂) = ⊃E' (wk' sub D₁) (wk' sub D₂)
  wk' sub (□I' D) = □I' D
  wk' sub (□E' D₁ s D₂) = □E' (wk' sub D₁) s (λ D₀ → wk' sub (D₂ D₀))
  wk' sub (◇I' ω D) = ◇I' ω D
  wk' sub (◇E' D₁ s D₂) = ◇E' (wk' sub D₁) s (λ ω D₀ → wk' sub (D₂ ω D₀)) 
  wk' sub (¬□I' D) = ¬□I' D
  wk' sub (¬□E' D₁ s D₂) = ¬□E' (wk' sub D₁) s (λ D₀ → wk' sub (D₂ D₀))
  wk' sub (¬◇I' ω D) = ¬◇I' ω D
  wk' sub (¬◇E' D₁ s D₂) = ¬◇E' (wk' sub D₁) s (λ ω D₀ → wk' sub (D₂ ω D₀))
 
  {- Substitution theorem -}

  subst' : ∀{Γ Δ w A s₁ s₂ C} 
      → ND w Γ Δ s₁ A
      → ND w (Γ , A [ w ]) Δ s₂ C
      → Σ λ s₃ → ND w Γ Δ s₃ C
  subst' D (hyp' i0) = ^ D
  subst' D (hyp' (iS iN)) = ^ hyp' iN
  subst' D (⊃I' D₁) = ^ ⊃I' (proj₂ (subst' (wk' wken D) (wk' exch D₁)))
  subst' D (⊃E' D₁ D₂) = ^ ⊃E' (proj₂ (subst' D D₁)) (proj₂ (subst' D D₂))
  subst' D (□I' D₁) = ^ □I' D₁
  subst' D (□E' D₁ s D₂) 
   = ^ □E' (proj₂ (subst' D D₁)) _ (λ D₀ → proj₂ (subst' D (D₂ D₀)))
  subst' D (◇I' ω D₁) = ^ ◇I' ω D₁
  subst' D (◇E' D₁ s D₂) 
   = ^ ◇E' (proj₂ (subst' D D₁)) _ (λ ω D₀ → proj₂ (subst' D (D₂ ω D₀))) 
  subst' D (¬□I' D₁) = ^ ¬□I' D₁
  subst' D (¬□E' D₁ s D₂) 
   = ^ ¬□E' (proj₂ (subst' D D₁)) _ (λ D₀ → proj₂ (subst' D (D₂ D₀)))
  subst' D (¬◇I' ω D₁) = ^ ¬◇I' ω D₁
  subst' D (¬◇E' D₁ s D₂) 
   = ^ ¬◇E' (proj₂ (subst' D D₁)) _ (λ ω D₀ → proj₂ (subst' D (D₂ ω D₀)))

  subst : ∀{Γ A w C} 
       → Γ ⊢ A [ w ] 
       → Γ , A [ w ] ⊢ C [ w ]
       → Γ ⊢ C [ w ]
  subst D E 
   = m→ (⊆to/↓ _) (proj₂ (subst' (proj₂ (→m refl D)) (proj₂ (→m extend↓ E))))

