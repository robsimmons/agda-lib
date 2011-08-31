-- Constructive Provability Logic 
-- Tethered intuitionstic variant
-- Robert J. Simmons, Bernardo Toninho

-- Natural deduction and substitution

module TetheredCPL.NatDeduction where
open import Prelude hiding (⊥)
open import Accessibility.Inductive
open import Accessibility.IndexedList
open import TetheredCPL.Core

module NAT-DEDUCTION (UWF : UpwardsWellFounded) where 
   open TRANS-UWF UWF
   open ILIST UWF
   open CORE UWF

   -- Weakening (outside the metric)
   wkP : W → Set
   wkP = λ w → ∀{Γ Γ' A} → Γ ⊆ Γ' to w → Γ ⊢ A [ w ] → Γ' ⊢ A [ w ]
  
   wk₁ : (w : W) → ((w' : W) → w ≺ w' → wkP w') → wkP w
   wk₁ w ih sub (hyp iN) = hyp (⊆to/now sub iN)
   wk₁ w ih sub (⊃I D) = ⊃I (wk₁ w ih (⊆to/both sub) D)
   wk₁ w ih sub (⊃E D₁ D₂) = ⊃E (wk₁ w ih sub D₁) (wk₁ w ih sub D₂)
   wk₁ w ih sub (⊥E D) = ⊥E (wk₁ w ih sub D)
   wk₁ w ih sub (◇I ω D) = ◇I ω (ih _ ω (⊆to/≺ ω sub) D)
   wk₁ w ih sub (◇E D D') = 
      ◇E (wk₁ w ih sub D) 
       (λ ω D₀ → wk₁ w ih sub (D' ω (ih _ ω (⊆to/≺' ω sub) D₀)))
   wk₁ w ih sub (□I D) = □I (λ ω → ih _ ω (⊆to/≺ ω sub) (D ω))
   wk₁ w ih sub (□E D₁ D₂) = 
      □E (wk₁ w ih sub D₁) 
       (λ D₀ → wk₁ w ih sub (D₂ (λ ω → ih _ ω (⊆to/≺' ω sub) (D₀ ω))))

   wk : ∀{Γ Γ' w A}
      → Γ ⊆ Γ' to w
      → Γ ⊢ A [ w ] 
      → Γ' ⊢ A [ w ]
   wk = ind wkP wk₁ _

   -- Metric
   data ND : (w : W) (Γ Δ : MCtx) → Shape Δ w → Type → Set where
      hyp' : ∀{w A Γ Δ} 
         → A at w ∈ Γ
         → ND w Γ Δ s0 (A)
      ⊃I' : ∀{w A B Γ Δ s}
         → ND w (A at w :: Γ) Δ s B
         → ND w Γ Δ (s1 s) (A ⊃ B)
      ⊃E' : ∀{B w A Γ Δ s₁ s₂}
         → ND w Γ Δ s₁ (A ⊃ B) 
         → ND w Γ Δ s₂ A
         → ND w Γ Δ (s2 s₁ s₂) B
      ⊥E' : ∀{w C Γ Δ s}
         → ND w Γ Δ s ⊥
         → ND w Γ Δ (s1 s) C
      ◇I' : ∀{Γ Δ A w w'}
         → w ≺ w'
         → Δ ⊢ A [ w' ]
         → ND w Γ Δ s0 (◇ A)
      ◇E' : ∀{Γ Δ A C w s₀}
         → ND w Γ Δ s₀ (◇ A)
         → (s : ∀{w'} → w ≺ w' → Δ ⊢ A [ w' ] → Shape Δ w)
         → (∀{w'} (ω : w ≺ w') (D₀ : Δ ⊢ A [ w' ]) → ND w Γ Δ (s ω D₀) C)
         → ND w Γ Δ (s2 s₀ (s◇⊢ s)) C
      □I' : ∀{w A Γ Δ}
         → (∀{w'} → w ≺ w' → Δ ⊢ A [ w' ]) 
         → ND w Γ Δ s0 (□ A) 
      □E' : ∀{w A Γ Δ C s₀}
         → ND w Γ Δ s₀ (□ A)
         → (s : (∀{w'} → w ≺ w' → Δ ⊢ A [ w' ]) → Shape Δ w)
         → ((D₀ : ∀{w'} → w ≺ w' → Δ ⊢ A [ w' ]) → ND w Γ Δ (s D₀) C)
         → ND w Γ Δ (s2 s₀ (s□⊢ s)) C

   -- Getting in and out of the metric
   m→ : ∀{Γ Δ w A s} → Δ ⊆ Γ to w → ND w Γ Δ s A → Γ ⊢ A [ w ]
   m→ sub (hyp' iN) = hyp iN
   m→ sub (⊃I' D) = ⊃I (m→ (⊆to/wken sub) D)
   m→ sub (⊃E' DA D) = ⊃E (m→ sub DA) (m→ sub D)
   m→ sub (⊥E' D) = ⊥E (m→ sub D)
   m→ sub (◇I' ω D) = ◇I ω (wk (⊆to/≺ ω sub) D)
   m→ sub (◇E' DA s D) = 
      ◇E (m→ sub DA) (λ ω D₀ → m→ sub (D ω (wk (⊆to/≺' ω sub) D₀)))
   m→ sub (□I' D) = □I (λ ω → wk (⊆to/≺ ω sub) (D ω) )
   m→ sub (□E' DA s D) = 
      □E (m→ sub DA) 
       (λ D₀ → m→ sub (D (λ ω → wk (⊆to/≺' ω sub) (D₀ ω))))

   →m : ∀{Γ w Δ A} → (Γ ↓ w) ≡ Δ → Γ ⊢ A [ w ] → ∃ λ s → ND w Γ Δ s A
   →m Refl (hyp iN) = , hyp' iN
   →m {Γ} Refl (⊃I D) = , ⊃I' (snd (→m extend↓ D))
   →m Refl (⊃E D₁ D₂) = , 
      ⊃E' (snd (→m refl D₁)) (snd (→m refl D₂)) 
   →m Refl (⊥E D) = , ⊥E' (snd (→m refl D))
   →m Refl (◇I ω D) = , ◇I' ω (wk (⊆to/↓≺ _ (≺+0 ω)) D)
   →m Refl (◇E D₁ D₂) = ,
      ◇E' (snd (→m refl D₁)) _ 
       (λ ω D₀ → snd (→m refl (D₂ ω (wk (⊆to/≺ ω (⊆to/↓ _)) D₀))))
   →m {Γ} Refl (□I D) = , □I' (λ ω → wk (⊆to/↓≺ Γ (≺+0 ω)) (D ω))
   →m {Γ} Refl (□E D₁ D₂) = , 
      □E' (snd (→m refl D₁)) _
       (λ D₀ → snd (→m refl (D₂ (λ ω → wk (⊆to/≺ ω (⊆to/↓ Γ)) (D₀ ω)))))

   -- Weakening (inside the metric)
   wk' : ∀{Γ Γ' w Δ s A}
      → Γ ⊆ Γ' to w
      → ND w Γ Δ s A 
      → ND w Γ' Δ s A
   wk' sub (hyp' iN) = hyp' (⊆to/now sub iN)
   wk' sub (⊃I' D) = ⊃I' (wk' (⊆to/both sub) D)
   wk' sub (⊃E' D₁ D₂) = ⊃E' (wk' sub D₁) (wk' sub D₂)
   wk' sub (⊥E' D) = ⊥E' (wk' sub D)
   wk' sub (◇I' ω D) = ◇I' ω D
   wk' sub (◇E' D₁ s D₂) = ◇E' (wk' sub D₁) s (λ ω D₀ → wk' sub (D₂ ω D₀)) 
   wk' sub (□I' D) = □I' D
   wk' sub (□E' D₁ s D₂) = □E' (wk' sub D₁) s (λ D₀ → wk' sub (D₂ D₀))
 
   -- Substitution theorem
   subst' : ∀{Γ Δ w A s₁ s₂ C} 
      → ND w Γ Δ s₁ A
      → ND w (A at w :: Γ) Δ s₂ C
      → ∃ λ s₃ → ND w Γ Δ s₃ C
   subst' D (hyp' Z) = , D
   subst' D (hyp' (S iN)) = , hyp' iN
   subst' D (⊃I' D₁) = , ⊃I' (snd (subst' (wk' wken D) (wk' exch D₁)))
   subst' D (⊃E' D₁ D₂) = , ⊃E' (snd (subst' D D₁)) (snd (subst' D D₂))
   subst' D (⊥E' D₁) = , ⊥E' (snd (subst' D D₁))
   subst' D (◇I' ω D₁) = , ◇I' ω D₁
   subst' D (◇E' D₁ s D₂) = ,
      ◇E' (snd (subst' D D₁)) _ (λ ω D₀ → snd (subst' D (D₂ ω D₀))) 
   subst' D (□I' D₁) = , □I' D₁
   subst' D (□E' D₁ s D₂) = , 
      □E' (snd (subst' D D₁)) _ (λ D₀ → snd (subst' D (D₂ D₀)))

   subst : ∀{Γ A w C} 
      → Γ ⊢ A [ w ] 
      → A at w :: Γ ⊢ C [ w ]
      → Γ ⊢ C [ w ]
   subst D E = 
      m→ (⊆to/↓ _) (snd (subst' (snd (→m refl D)) (snd (→m extend↓ E))))
