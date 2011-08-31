-- Constructive Provability Logic 
-- The minimal, modal, propositional fragment
-- Robert J. Simmons, Bernardo Toninho

-- Soundness and completeness of the sequent calculus

-- Uncomment this to make the file load faster:
-- {-# OPTIONS --no-termination-check #-}

module MinimalCPL.Sequent where
open import Prelude
open import Accessibility.Inductive 
open import Accessibility.IndexedList
open import MinimalCPL.Core 

module SEQUENT (UWF : UpwardsWellFounded) where
   open TRANS-UWF UWF
   open ILIST UWF
   open CORE UWF 

   -- Weakening (outside the metric)
   wkP : W → Set
   wkP = λ w → ∀{Γ Γ' A} → Γ ⊆ Γ' to w → Γ ⇒ A [ w ] → Γ' ⇒ A [ w ]
  
   wk₁ : (w : W) → ((w' : W) → w ≺ w' → wkP w') → wkP w
   wk₁ w ih sub (hyp iN) = hyp (⊆to/now sub iN)
   wk₁ w ih sub (⊃R D) = ⊃R (wk₁ w ih (⊆to/both sub) D)
   wk₁ w ih sub (⊃L iN D D') = 
      ⊃L (⊆to/now sub iN) (wk₁ w ih sub D) (wk₁ w ih (⊆to/both sub) D')
   wk₁ w ih sub (◇R ω D) = ◇R ω (ih _ ω (⊆to/≺ ω sub) D)
   wk₁ w ih sub (◇L iN D) = 
      ◇L (⊆to/now sub iN)
       (λ ω D₀ → wk₁ w ih sub (D ω (ih _ ω (⊆to/≺' ω sub) D₀)))
   wk₁ w ih sub (□R D) = □R (λ ω → ih _ ω (⊆to/≺ ω sub) (D ω))
   wk₁ w ih sub (□L iN D) = 
      □L (⊆to/now sub iN) 
       (λ D₀ → wk₁ w ih sub (D (λ ω → ih _ ω (⊆to/≺' ω sub) (D₀ ω))))
   wk₁ w ih sub (¬◇R D) = ¬◇R (λ ω D₀ → D ω (ih _ ω (⊆to/≺' ω sub) D₀))
   wk₁ w ih sub (¬◇L iN D) = 
      ¬◇L (⊆to/now sub iN) 
       (λ D₀ → wk₁ w ih sub (D (λ ω D' → D₀ ω (ih _ ω (⊆to/≺ ω sub) D'))))
   wk₁ w ih sub (¬□R ω D) = ¬□R ω (λ D₀ → D (ih _ ω (⊆to/≺' ω sub) D₀))
   wk₁ w ih sub (¬□L iN D) = 
      ¬□L (⊆to/now sub iN) 
       (λ ω D₀ → wk₁ w ih sub (D ω (λ D' → D₀ (ih _ ω (⊆to/≺ ω sub) D'))))
 
   wk : ∀{Γ Γ' w A}
      → Γ ⊆ Γ' to w
      → Γ ⇒ A [ w ] 
      → Γ' ⇒ A [ w ]
   wk = ind wkP wk₁ _
 
   -- Metric
   data Seq : (w : W) (Γ Δ : MCtx) → Shape Δ w → Type → Set where
      hyp' : ∀{w Q Γ Δ} 
         → a Q at w ∈ Γ
         → Seq w Γ Δ s0 (a Q)
      ⊃R' : ∀{w A B Γ Δ s}
         → Seq w (A at w :: Γ) Δ s B
         → Seq w Γ Δ (s1 s) (A ⊃ B)
      ⊃L' : ∀{B w A C Γ Δ s₁ s₂}
         → ((A ⊃ B) at w) ∈ Γ
         → Seq w Γ Δ s₁ A 
         → Seq w (B at w :: Γ) Δ s₂ C
         → Seq w Γ Δ (s2 s₁ s₂) C
      ◇R' : ∀{w Γ Δ w' A}
         → w ≺ w'
         → Δ ⇒ A [ w' ]
         → Seq w Γ Δ s0 (◇ A)
      ◇L' : ∀{w Γ Δ C A}
         → (◇ A) at w ∈ Γ
         → (s : ∀{w'} → w ≺ w' → Δ ⇒ A [ w' ] → Shape Δ w)
         → (∀{w'} (ω : w ≺ w') (D₀ : Δ ⇒ A [ w' ]) → Seq w Γ Δ (s ω D₀) C)
         → Seq w Γ Δ (s◇⇒ s) C
      □R' : ∀{w A Γ Δ}
         → (∀{w'} → w ≺ w' → Δ ⇒ A [ w' ]) 
         → Seq w Γ Δ s0 (□ A) 
      □L' : ∀{w A Γ Δ C}
         → (□ A) at w ∈ Γ
         → (s : (∀{w'} → w ≺ w' → Δ ⇒ A [ w' ]) → Shape Δ w)
         → ((D₀ : ∀{w'} → w ≺ w' → Δ ⇒ A [ w' ]) → Seq w Γ Δ (s D₀) C)
         → Seq w Γ Δ (s□⇒ s) C
      ¬◇R' : ∀{w A Γ Δ}
         → (∀{w'} → w ≺ w' → Δ ⇒ A [ w' ] → Void) 
         → Seq w Γ Δ s0 (¬◇ A) 
      ¬◇L' : ∀{w A Γ Δ C}
         → (¬◇ A) at w ∈ Γ
         → (s : (∀{w'} → w ≺ w' → Δ ⇒ A [ w' ] → Void) → Shape Δ w)
         → ((D₀ : ∀{w'} → w ≺ w' → Δ ⇒ A [ w' ] → Void) → Seq w Γ Δ (s D₀) C)
         → Seq w Γ Δ (s¬◇⇒ s) C
      ¬□R' : ∀{w Γ Δ w' A}
         → w ≺ w'
         → (Δ ⇒ A [ w' ] → Void)
         → Seq w Γ Δ s0 (¬□ A)
      ¬□L' : ∀{w Γ Δ C A}
         → (¬□ A) at w ∈ Γ
         → (s : ∀{w'} → w ≺ w' → (Δ ⇒ A [ w' ] → Void) → Shape Δ w)
         → (∀{w'} (ω : w ≺ w') (D₀ : Δ ⇒ A [ w' ] → Void) 
            → Seq w Γ Δ (s ω D₀) C)
         → Seq w Γ Δ (s¬□⇒ s) C

   -- Getting into and out of the metric
   m→ : ∀{Γ Δ w A s} → Δ ⊆ Γ to w → Seq w Γ Δ s A → Γ ⇒ A [ w ]
   m→ sub (hyp' iN) = hyp iN
   m→ sub (⊃R' D) = ⊃R (m→ (⊆to/wken sub) D)
   m→ sub (⊃L' iN D D') = ⊃L iN (m→ sub D) (m→ (⊆to/wken sub) D')
   m→ sub (◇R' ω D) = ◇R ω (wk (⊆to/≺ ω sub) D)
   m→ sub (◇L' ω s D) = 
      ◇L ω (λ ω D₀ → m→ sub (D ω (wk (⊆to/≺' ω sub) D₀)))
   m→ sub (□R' D) = □R (λ ω → wk (⊆to/≺ ω sub) (D ω))
   m→ sub (□L' iN s D) = 
      □L iN (λ D₀ → m→ sub (D (λ ω → wk (⊆to/≺' ω sub) (D₀ ω))))
   m→ sub (¬◇R' D) = ¬◇R (λ ω D₀ → D ω (wk (⊆to/≺' ω sub) D₀))
   m→ sub (¬◇L' iN s D) =
      ¬◇L iN (λ D₀ → m→ sub (D (λ ω D' → D₀ ω (wk (⊆to/≺ ω sub) D'))))
   m→ sub (¬□R' ω D) = ¬□R ω (λ D₀ → D (wk (⊆to/≺' ω sub) D₀))
   m→ sub (¬□L' ω s D) = 
      ¬□L ω (λ ω D₀ → m→ sub (D ω (λ D' → D₀ (wk (⊆to/≺ ω sub) D'))))

   →m : ∀{Γ w Δ A} → (Γ ↓ w) ≡ Δ → Γ ⇒ A [ w ] → ∃ λ s → Seq w Γ Δ s A
   →m Refl (hyp iN) = , hyp' iN
   →m Refl (⊃R D) = , ⊃R' (snd (→m extend↓ D))
   →m Refl (⊃L iN D D') = , ⊃L' iN (snd (→m refl D)) (snd (→m extend↓ D'))
   →m Refl (◇R ω D) = , ◇R' ω (wk (⊆to/↓≺ _ (≺+0 ω)) D)
   →m {Γ} Refl (◇L iN D) = , 
      ◇L' iN _ 
       (λ ω D₀ → snd (→m refl (D ω (wk (⊆to/≺ ω (⊆to/↓ _)) D₀))))
   →m {Γ} Refl (□R D) = , □R' (λ ω → wk (⊆to/↓≺ Γ (≺+0 ω)) (D ω))
   →m {Γ} Refl (□L iN D) = ,
      □L' iN _ 
       (λ D₀ → snd (→m refl (D (λ ω → wk (⊆to/≺ ω (⊆to/↓ Γ)) (D₀ ω)))))
   →m Refl (¬◇R D) = , ¬◇R' (λ ω D₀ → D ω (wk (⊆to/≺ ω (⊆to/↓ _)) D₀))
   →m Refl (¬◇L iN D) = ,
      ¬◇L' iN _ (λ D₀ → snd
       (→m refl (D (λ ω D' → D₀ ω (wk (⊆to/↓≺ _ (≺+0 ω)) D')))))
   →m Refl (¬□R ω D) = , ¬□R' ω (λ D₀ → D (wk (⊆to/≺ ω (⊆to/↓ _)) D₀))
   →m Refl (¬□L iN D) = ,
      ¬□L' iN _ (λ ω D₀ → snd 
       (→m refl (D ω (λ D' → D₀ (wk (⊆to/↓≺ _ (≺+0 ω)) D')))))

   -- Weakening (inside the metric)
   wk' : ∀{Γ' Γ Δ A w s} 
      → Γ ⊆ Γ' to w
      → Seq w Γ Δ s A 
      → Seq w Γ' Δ s A
   wk' sub (hyp' iN) = hyp' (⊆to/now sub iN)
   wk' sub (⊃R' D) = ⊃R' (wk' (⊆to/both sub) D)
   wk' sub (⊃L' iN D D') = 
      ⊃L' (⊆to/now sub iN) (wk' sub D) (wk' (⊆to/both sub) D')
   wk' sub (◇R' ω D) = ◇R' ω D
   wk' sub (◇L' iN s D) = ◇L' (⊆to/now sub iN) _ (λ ω D₀ → wk' sub (D ω D₀))
   wk' sub (□R' D) = □R' D
   wk' sub (□L' iN s D) = 
      □L' (⊆to/now sub iN) _ (λ D₀ → wk' sub (D (λ ω → D₀ ω)))
   wk' sub (¬◇R' D) = ¬◇R' D
   wk' sub (¬◇L' iN s D) = ¬◇L' (⊆to/now sub iN) _ (λ D₀ → wk' sub (D D₀))
   wk' sub (¬□R' ω D) = ¬□R' ω D
   wk' sub (¬□L' iN s D) = ¬□L' (⊆to/now sub iN) _ (λ ω D₀ → wk' sub (D ω D₀))
   
   -- Admissibility of cut (tethered)
   cut' : ∀{Γ Δ w A s₁ s₂ C} 
      → Seq w Γ Δ s₁ A
      → Seq w (A at w :: Γ) Δ s₂ C
      → ∃ λ s₃ → Seq w Γ Δ s₃ C
   cut' (hyp' iN) (hyp' Z) = , hyp' iN
   cut' (⊃R' D) (⊃L' Z EA E) with cut' (⊃R' D) EA | cut' (wk' wken (⊃R' D)) 
                                                          (wk' exch E)
   ... | _ , EA' | _ , E' = cut' (snd (cut' EA' D)) E'
   cut' (◇R' ω D) (◇L' Z s E) = cut' (◇R' ω D) (E ω D)
   cut' (□R' D) (□L' Z s E) = cut' (□R' D) (E D)
   cut' (¬◇R' D) (¬◇L' Z s E) = cut' (¬◇R' D) (E D)
   cut' (¬□R' ω D) (¬□L' Z s E) = cut' (¬□R' ω D) (E ω D)

   -- Left commutative cuts
   cut' (⊃L' iN DA D) E = , ⊃L' iN DA (snd (cut' D (wk' wkex E)))
   cut' (◇L' iN s D) E = , ◇L' iN _ (λ ω D₀ → snd (cut' (D ω D₀) E))
   cut' (□L' iN s D) E = , □L' iN _ (λ D₀ → snd (cut' (D D₀) E))
   cut' (¬◇L' iN s D) E = , ¬◇L' iN _ (λ D₀ → snd (cut' (D D₀) E))
   cut' (¬□L' iN s D) E = , ¬□L' iN _ (λ ω D₀ → snd (cut' (D ω D₀) E))

   -- Right commutative cuts
   cut' D (hyp' (S iN)) = , hyp' iN
   cut' D (⊃R' E) = , ⊃R' (snd (cut' (wk' wken D) (wk' exch E)))
   cut' D (⊃L' (S iN) EA E) = , 
      ⊃L' iN (snd (cut' D EA)) (snd (cut' (wk' wken D) (wk' exch E)))
   cut' D (◇R' ω E) = , ◇R' ω E
   cut' D (◇L' (S iN) s E) = , ◇L' iN _ (λ ω D₀ → snd (cut' D (E ω D₀)))
   cut' D (□R' E) = , □R' E
   cut' D (□L' (S iN) s E) = , □L' iN _ (λ D₀ → snd (cut' D (E D₀)))
   cut' D (¬◇R' E) = , ¬◇R' E
   cut' D (¬◇L' (S iN) s E) = , ¬◇L' iN _ (λ D₀ → snd (cut' D (E D₀)))
   cut' D (¬□R' ω E) = , ¬□R' ω E
   cut' D (¬□L' (S iN) s E) = , ¬□L' iN _ (λ ω D₀ → snd (cut' D (E ω D₀)))

   cut : ∀{Γ w A C} → Γ ⇒ A [ w ] → A at w :: Γ ⇒ C [ w ] → Γ ⇒ C [ w ]
   cut D E = 
      m→ (⊆to/↓ _) (snd (cut' (snd (→m refl D)) (snd (→m extend↓ E))))

   -- The identity theorem
   iden : ∀{w Γ}(A : _) → A at w :: Γ ⇒ A [ w ]
   iden (a N) = hyp Z
   iden (A ⊃ B) = ⊃R (⊃L (S Z) (iden A) (iden B))
   iden (◇ A) = ◇L Z ◇R
   iden (□ A) = □L Z □R
   iden (¬◇ A) = ¬◇L Z ¬◇R
   iden (¬□ A) = ¬□L Z ¬□R

   iden' : ∀{w Γ}(A : _) → (A at w) ∈ Γ → Γ ⇒ A [ w ]
   iden' (a N) iN = hyp iN
   iden' (A ⊃ B) iN = ⊃R (⊃L (S iN) (iden A) (iden B))
   iden' (◇ A) iN = ◇L iN ◇R
   iden' (□ A) iN = □L iN □R
   iden' (¬◇ A) iN = ¬◇L iN ¬◇R
   iden' (¬□ A) iN = ¬□L iN ¬□R
