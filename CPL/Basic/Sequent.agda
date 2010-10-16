-- KS4⁻ Sequent Calculus
-- A Constructive Logic of Provability
-- Robert J. Simmons, Bernardo Toninho

-- Uncomment this to make the file load faster:
{-# OPTIONS --no-termination-check #-}

open import Compat
open import Accessibility.Inductive 
import Accessibility.IndexedList as IndexedList
import Basic.Core as Core 

module Basic.Sequent (UWF : UpwardsWellFounded) where 

  open SuccStar UWF
  open IndexedList UWF
  open Core UWF 

  {- Weakening (outside the metric) -}

  wkP : W → Set
  wkP = λ w → ∀{Γ Γ' A} → Γ ⊆ Γ' to w → Γ ⇒ A [ w ] → Γ' ⇒ A [ w ]
  
  wk₁ : (w : W) → ((w' : W) → w ≺ w' → wkP w') → wkP w
  wk₁ w ih sub (hyp iN) = hyp (⊆to/now sub iN)
  wk₁ w ih sub (⊃R D) = ⊃R (wk₁ w ih (⊆to/both sub) D)
  wk₁ w ih sub (⊃L iN D D') 
   = ⊃L (⊆to/now sub iN) (wk₁ w ih sub D) (wk₁ w ih (⊆to/both sub) D')
  wk₁ w ih sub (□R D) = □R (λ ω → ih _ ω (⊆to/≺ (≺+0 ω) sub) (D ω))
  wk₁ w ih sub (□L iN D) 
   = □L (⊆to/now sub iN) 
      (λ D₀ → wk₁ w ih sub (D (λ ω → ih _ ω (⊆to/≺' (≺+0 ω) sub) (D₀ ω))))
  wk₁ w ih sub (◇R ω D) = ◇R ω (ih _ ω (⊆to/≺ (≺+0 ω) sub) D)
  wk₁ w ih sub (◇L iN D)
   = ◇L (⊆to/now sub iN)
      (λ ω D₀ → wk₁ w ih sub (D ω (ih _ ω (⊆to/≺' (≺+0 ω) sub) D₀)))
  wk₁ w ih sub (⊥L iN) = ⊥L (⊆to/now sub iN) 
 
  wk : ∀{Γ Γ' w A}
       → Γ ⊆ Γ' to w
       → Γ ⇒ A [ w ] 
       → Γ' ⇒ A [ w ]
  wk = ind wkP wk₁ _
 

  {- Metric -}

  data Seq : (w : W) (Γ Δ : MCtx) → Shape Δ w → Type → Set where
    hyp' : ∀{w Q Γ Δ} 
      → a Q at w ∈ Γ
      → Seq w Γ Δ s0 (a Q)
    ⊃R' : ∀{w A B Γ Δ s}
      → Seq w (Γ , A [ w ]) Δ s B
      → Seq w Γ Δ (s1 s) (A ⊃ B)
    ⊃L' : ∀{B w A C Γ Δ s₁ s₂}
      → ((A ⊃ B) at w) ∈ Γ
      → Seq w Γ Δ s₁ A 
      → Seq w (Γ , B [ w ]) Δ s₂ C
      → Seq w Γ Δ (s2 s₁ s₂) C
    □R' : ∀{w A Γ Δ}
      → (∀{w'} → w ≺ w' → Δ ⇒ A [ w' ]) 
      → Seq w Γ Δ s0 (□ A) 
    □L' : ∀{w A Γ Δ C}
      → (□ A) at w ∈ Γ
      → (s : (∀{w'} → w ≺ w' → Δ ⇒ A [ w' ]) → Shape Δ w)
      → ((D₀ : ∀{w'} → w ≺ w' → Δ ⇒ A [ w' ]) → Seq w Γ Δ (s D₀) C)
      → Seq w Γ Δ (s□⇒ s) C
    ◇R' : ∀{w Γ Δ w' A}
      → w ≺ w'
      → Δ ⇒ A [ w' ]
      → Seq w Γ Δ s0 (◇ A)
    ◇L' : ∀{w Γ Δ C A}
      → (◇ A) at w ∈ Γ
      → (s : ∀{w'} → w ≺ w' → Δ ⇒ A [ w' ] → Shape Δ w)
      → (∀{w'} (ω : w ≺ w') (D₀ : Δ ⇒ A [ w' ]) → Seq w Γ Δ (s ω D₀) C)
      → Seq w Γ Δ (s◇⇒ s) C
    ⊥L' : ∀{w Γ Δ C}
      → ⊥ at w ∈ Γ
      → Seq w Γ Δ s0 C

  -- Getting into and out of the metric
  m→ : ∀{Γ Δ w A s} → Δ ⊆ Γ to w → Seq w Γ Δ s A → Γ ⇒ A [ w ]
  m→ sub (hyp' iN) = hyp iN
  m→ sub (⊃R' D) = ⊃R (m→ (⊆to/wken sub) D)
  m→ sub (⊃L' iN D D') = ⊃L iN (m→ sub D) (m→ (⊆to/wken sub) D')
  m→ sub (□R' D) = □R (λ ω → wk (⊆to/≺ (≺+0 ω) sub) (D ω))
  m→ sub (□L' iN s D)
   = □L iN (λ D₀ → m→ sub (D (λ ω → wk (⊆to/≺' (≺+0 ω) sub) (D₀ ω))))
  m→ sub (◇R' ω D) = ◇R ω (wk (⊆to/≺ (≺+0 ω) sub) D)
  m→ sub (◇L' ω s D) 
   = ◇L ω (λ ω D₀ → m→ sub (D ω (wk (⊆to/≺' (≺+0 ω) sub) D₀)))
  m→ sub (⊥L' iN) = ⊥L iN

  →m : ∀{Γ w Δ A} → (Γ ↓ w) ≡ Δ → Γ ⇒ A [ w ] → Σ λ s → Seq w Γ Δ s A
  →m refl (hyp iN) = ^ hyp' iN
  →m refl (⊃R D) = ^ ⊃R' (proj₂ (→m extend↓ D))
  →m refl (⊃L iN D D') = ^ ⊃L' iN (proj₂ (→m refl D)) (proj₂ (→m extend↓ D'))
  →m {Γ} refl (□R D) = ^ □R' (λ ω → wk (⊆to/↓≺ Γ (≺+0 ω)) (D ω))
  →m {Γ} refl (□L iN D) 
   = ^ □L' iN _ 
      (λ D₀ → proj₂ (→m refl (D (λ ω → wk (⊆to/≺ (≺+0 ω) (⊆to/↓ Γ)) (D₀ ω)))))
  →m refl (◇R ω D) = ^ ◇R' ω (wk (⊆to/↓≺ _ (≺+0 ω)) D)
  →m {Γ} refl (◇L iN D) 
   = ^ ◇L' iN _ 
      (λ ω D₀ → proj₂ (→m refl (D ω (wk (⊆to/≺ (≺+0 ω) (⊆to/↓ _)) D₀))))
  →m refl (⊥L iN) = ^ ⊥L' iN 


  {- Weakening (inside the metric) -}

  wk' : ∀{Γ' Γ Δ A w s} 
      → Γ ⊆ Γ' to w
      → Seq w Γ Δ s A 
      → Seq w Γ' Δ s A
  wk' sub (hyp' iN) = hyp' (⊆to/now sub iN)
  wk' sub (⊃R' D) = ⊃R' (wk' (⊆to/both sub) D)
  wk' sub (⊃L' iN D D') 
   = ⊃L' (⊆to/now sub iN) (wk' sub D) (wk' (⊆to/both sub) D')
  wk' sub (□R' D) = □R' D
  wk' sub (□L' iN s D) 
   = □L' (⊆to/now sub iN) _ (λ D₀ → wk' sub (D (λ ω → D₀ ω)))
  wk' sub (◇R' ω D) = ◇R' ω D
  wk' sub (◇L' iN s D) = ◇L' (⊆to/now sub iN) _ (λ ω D₀ → wk' sub (D ω D₀))
  wk' sub (⊥L' iN) = ⊥L' (⊆to/now sub iN)
  
 
  {- Admissibility of cut (tethered) -}

  cut' : ∀{Γ Δ w A s₁ s₂ C} 
      → Seq w Γ Δ s₁ A
      → Seq w (Γ , A [ w ]) Δ s₂ C
      → Σ λ s₃ → Seq w Γ Δ s₃ C
  cut' (hyp' iN) (hyp' i0) = ^ hyp' iN
  cut' (⊃R' D) (⊃L' i0 EA E) with cut' (⊃R' D) EA | cut' (wk' wken (⊃R' D)) 
                                                          (wk' exch E)
  ... | _ ^ EA' | _ ^ E' = cut' (proj₂ (cut' EA' D)) E'
  cut' (□R' D) (□L' i0 s E) = cut' (□R' D) (E D)
  cut' (◇R' ω D) (◇L' i0 s E) = cut' (◇R' ω D) (E ω D)

  -- Left commutative cuts
  cut' (⊃L' iN DA D) E = ^ ⊃L' iN DA (proj₂ (cut' D (wk' wkex E)))
  cut' (□L' iN s D) E = ^ □L' iN _ (λ D₀ → proj₂ (cut' (D D₀) E))
  cut' (◇L' iN s D) E = ^ ◇L' iN _ (λ ω D₀ → proj₂ (cut' (D ω D₀) E))
  cut' (⊥L' iN) E = ^ ⊥L' iN 

  -- Right commutative cuts
  cut' D (hyp' (iS iN)) = ^ hyp' iN
  cut' D (⊃R' E) = ^ ⊃R' (proj₂ (cut' (wk' wken D) (wk' exch E)))
  cut' D (⊃L' (iS iN) EA E) 
   = ^ ⊃L' iN (proj₂ (cut' D EA)) (proj₂ (cut' (wk' wken D) (wk' exch E)))
  cut' D (□R' E) = ^ □R' E
  cut' D (□L' (iS iN) s E) = ^ □L' iN _ (λ D₀ → proj₂ (cut' D (E D₀)))
  cut' D (◇R' ω E) = ^ ◇R' ω E
  cut' D (◇L' (iS iN) s E) = ^ ◇L' iN _ (λ ω D₀ → proj₂ (cut' D (E ω D₀)))
  cut' D (⊥L' (iS iN)) = ^ ⊥L' iN 

  cut : ∀{Γ w A C} → Γ ⇒ A [ w ] → Γ , A [ w ] ⇒ C [ w ] → Γ ⇒ C [ w ]
  cut D E 
   = m→ (⊆to/↓ _) (proj₂ (cut' (proj₂ (→m refl D)) (proj₂ (→m extend↓ E))))

  
  {- The identity theorem -} 

  iden : ∀{w Γ}(A : _) → (Γ , A [ w ] ⇒ A [ w ])
  iden (a N) = hyp i0
  iden (A ⊃ B) = ⊃R (⊃L (iS i0) (iden A) (iden B))
  iden (□ A) = □L i0 □R
  iden (◇ A) = ◇L i0 ◇R
  iden ⊥ = ⊥L i0

  iden' : ∀{w Γ}(A : _) → (A at w) ∈ Γ → Γ ⇒ A [ w ]
  iden' (a N) iN = hyp iN
  iden' (A ⊃ B) iN = ⊃R (⊃L (iS iN) (iden A) (iden B))
  iden' (□ A) iN = □L iN □R
  iden' (◇ A) iN = ◇L iN ◇R
  iden' ⊥ iN = ⊥L iN