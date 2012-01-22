-- Constructive Provability Logic  
-- De-tethered intuitionstic variant
-- Robert J. Simmons, Bernardo Toninho

-- Valid and invalid axioms

module DetetheredCPL.Axioms where
open import Prelude hiding (⊥ ; ¬)
open import Accessibility.Inductive
open import Accessibility.Three
open import Accessibility.IndexedList
open import DetetheredCPL.Core renaming (Type to UType)
open import FocusedCPL.Core
open import FocusedCPL.Cut
open import FocusedCPL.Identity
open import DetetheredCPL.Equiv

Ctx = List UType

¬ : UType → UType
¬ A = A ⊃ ⊥

module PROPERTIES (UWF : UpwardsWellFounded) where
   open TRANS-UWF UWF
   open CORE UWF 

   Trans : Set
   Trans = ∀{w₁ w₂ w₃} → w₁ ≺ w₂ → w₂ ≺ w₃ → w₁ ≺ w₃


module AXIOMS (UWF : UpwardsWellFounded) where
   open TRANS-UWF UWF
   open PROPERTIES UWF
   open ILIST UWF
   open CORE UWF 
   
 -- Axioms of intuitionstic propositional logic (Theorem 3.1)
   axI : ∀{Γ A w} 
      → Γ ⊢ A ⊃ A [ w ]
   axI = ⊃I (hyp Z)

   axK : ∀{Γ A B w}
      → Γ ⊢ A ⊃ B ⊃ A [ w ]
   axK = ⊃I (⊃I (hyp (S Z)))

   axS : ∀{Γ A B C w}
      → Γ ⊢ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C [ w ]
   axS = ⊃I (⊃I (⊃I (⊃E (⊃E (hyp (S (S Z))) (hyp Z)) (⊃E (hyp (S Z)) (hyp Z)))))
   
   ax⊥E : ∀{Γ A w}
      → Γ ⊢ ⊥ ⊃ A [ w ]
   ax⊥E = ⊃I (⊥E ≺*≡ (hyp Z))

 -- Necessitation rule (Theorem 3.2)
   Nec : ∀{Γ A} 
      → (∀{w} → Γ ⊢ A [ w ])
      → (∀{w} → Γ ⊢ □ A [ w ])
   Nec D = □I (λ ω → D) 
    
 -- Axioms of IK, Simpson's intuitionistic modal logic (Theorem 3.3)
   axK□ : ∀{Γ A B w}
      → Γ ⊢ □ (A ⊃ B) ⊃ □ A ⊃ □ B [ w ]
   axK□ = ⊃I (⊃I (□E ≺*≡ (hyp (S Z)) 
      (λ D₀ → □E ≺*≡ (hyp Z) 
      (λ D₀' → □I (λ ω → ⊃E (D₀ ω) (D₀' ω))))))

   axK◇ : ∀{Γ A B w}
      → Γ ⊢ □ (A ⊃ B) ⊃ ◇ A ⊃ ◇ B [ w ]
   axK◇ = ⊃I (⊃I (◇E ≺*≡ (hyp Z) 
      (λ ω D₀ → □E ≺*≡ (hyp (S Z)) 
      (λ D₀' → ◇I ω (⊃E (D₀' ω) D₀)))))

   ax4□ : ∀{Γ A w}
      → Trans
      → Γ ⊢ □ A ⊃ □ (□ A) [ w ]
   ax4□ _≺≺_ = ⊃I (□E ≺*≡ (hyp Z) 
      λ D → □I λ ω → □I λ ω' → D (ω ≺≺ ω'))
 

   ax◇⊥ : ∀{Γ w}
      → Γ ⊢ ¬ (◇ ⊥) [ w ]
   ax◇⊥ = ⊃I (◇E ≺*≡ (hyp Z) 
      (λ ω D₀ → ⊥E (≺*+ (≺+0 ω)) D₀))


   ax4◇ : ∀{Γ A w}
      → Trans
      → Γ ⊢ ◇ (◇ A) ⊃ ◇ A [ w ]
   ax4◇  _≺≺_ = ⊃I (◇E ≺*≡ (hyp Z) 
      (λ ω D₀ → ◇E (≺*+ (≺+0 ω)) D₀ 
      (λ ω' D₀' → ◇I (ω ≺≺ ω') D₀')))

 -- Axiom GL (Theorem 3.4)
   axGL : ∀{Γ A w}
      → Trans
      → Γ ⊢ □ (□ A ⊃ A) ⊃ □ A [ w ]
   axGL {A = A} _≺≺_ = ind P lemma _
    where
      P : W → Set
      P = λ w → ∀{Γ} → Γ ⊢ □ (□ A ⊃ A) ⊃ □ A [ w ]
   
      lemma : (w : W) → ((w' : W) → w ≺ w' → P w') → P w
      lemma w ih = ⊃I (□E ≺*≡ (hyp Z) 
         λ DInd → □I 
         λ ω → ⊃E (DInd ω) (⊃E (ih _ ω) (□I (λ ω' → DInd (ω ≺≺ ω')))))

 -- Löb rule (Theorem 3.5)
  
   Löb : ∀{Γ A}  
       → (∀{w} → Γ ⊢ □ A ⊃ A [ w ])
       → (∀{w} → Γ ⊢ A [ w ])
   Löb D = ind LöbP Löb' _ D
    where 
      LöbP : W → Set
      LöbP = λ w → ∀{Γ A} → (∀{w} → Γ ⊢ (□ A) ⊃ A [ w ]) → Γ ⊢ A [ w ]

      Löb' : (w : W) → ((w' : W) → w ≺ w' → LöbP w') → LöbP w
      Löb' w ih D = ⊃E D (□I (λ ω → ih _ ω D))

 -- De Morgan laws (Theorem 3.6)
   ax◇¬ : ∀{Γ A w}  
      → Γ ⊢ ◇ (¬ A) ⊃ ¬ (□ A) [ w ]
   ax◇¬  = ⊃I (⊃I (□E ≺*≡ (hyp Z) 
      (λ D₀ → ◇E ≺*≡ (hyp (S Z)) 
      (λ ω D₀' → ⊥E (≺*+ (≺+0 ω)) (⊃E D₀' (D₀ ω))))))


   ax□¬ : ∀{Γ A w} 
      → Γ ⊢ □ (¬ A) ⊃ ¬ (◇ A) [ w ]
   ax□¬ = ⊃I (⊃I (◇E ≺*≡ (hyp Z) 
      (λ ω D₀ → □E ≺*≡ (hyp (S Z)) 
      (λ D₀' → ⊥E (≺*+ (≺+0 ω)) (⊃E (D₀' ω) D₀)))))

module NON-AXIOMS where
   open TRANS-UWF SmallExample
   open PROPERTIES SmallExample
   open ILIST SmallExample
   open CORE SmallExample
   open SEQUENT SmallExample

   dec≺ : (w w' : Three) → Decidable (w ≺* w')
   dec≺ α α = Inl ≺*≡
   dec≺ α β = Inl (≺*+ (≺+0 αβ))
   dec≺ α γ = Inl (≺*+ (≺+0 αγ))
   dec≺ β α = Inr (≺⊀ αβ)
   dec≺ β β = Inl ≺*≡
   dec≺ β γ = Inl (≺*+ (≺+0 βγ))
   dec≺ γ α = Inr (≺⊀ αγ)
   dec≺ γ β = Inr (≺⊀ βγ)
   dec≺ γ γ = Inl ≺*≡

   open EQUIV SmallExample dec≺
  
   Q : UType
   Q = a "Q" ⁺   

   Q⁺ : Type ⁺
   Q⁺ = a "Q" ⁺   

 -- Axioms of IK, Simpson's intuitionistic modal logic (Theorem 3.3)
   axIK : [] ⊢ (◇ Q ⊃ □ ⊥) ⊃ □ (Q ⊃ ⊥) [ β ] → Void
   axIK D = lem (foc D)
    where
     lem : 
       Term [] β · (Reg (↓ (◇ Q⁺ ⊃ ↑ (□ ⊥)) ⊃ ↑ (□ (↓ (Q⁺ ⊃ ↑ ⊥))))) 
       → Void
     lem (⊃R (L <> (↓L <> _ Z (⊃L (◇R βγ (↓L _ (≺*+ (≺+0 ())) Z _)) _)))) 
     lem (⊃R (L <> (↓L <> _ Z (⊃L (◇R βγ (↓L _ (≺*+ (≺+S () _)) Z _)) _))))
     lem (⊃R (L <> (↓L <> _ Z (⊃L (◇R βγ (↓L _ _ (S ()) _)) _)))) 
     lem (⊃R (L <> (↓L <> _ Z (⊃L (◇R βy (↑R (pR (S ())))) _)))) 
     lem (⊃R (L <> (↓L <> _ (S ()) Sp)))
     lem (↓L () ωh x Sp)
     lem (⊃R (L <> (↑R (□R N₁)))) with N₁ βγ
     ... | ↓L <> (≺*+ (≺+0 ())) Z Sp
     ... | ↓L <> (≺*+ (≺+S () y')) Z Sp
     ... | ↓L <> ωh (S ()) Sp
     ... | ↑R (↓R (↓L pf⁻ (≺*+ (≺+0 ())) Z Sp))
     ... | ↑R (↓R (↓L pf⁻ (≺*+ (≺+S () y')) Z Sp))
     ... | ↑R (↓R (↓L pf⁻ ωh (S ()) Sp))
     ... | ↑R (↓R (⊃R (L <> (↓L <> (≺*+ (≺+0 ())) (S Z) Sp))))
     ... | ↑R (↓R (⊃R (L <> (↓L <> (≺*+ (≺+S () y')) (S Z) Sp))))
     ... | ↑R (↓R (⊃R (L <> (↓L <> ωh (S (S ())) Sp))))
     ... | ↑R (↓R (⊃R (L <> (↑R ()))))

 -- De Morgan laws (Theorem 3.6)
   ax¬◇ : [] ⊢ ¬ (◇ Q) ⊃ □(¬ Q) [ β ] → Void
   ax¬◇ D = lem (foc D) 
    where
     lem : 
       Term [] β · (Reg (↓ (◇ (a "Q" ⁺) ⊃ ↑ ⊥) ⊃ ↑ (□ (↓ (a "Q" ⁺ ⊃ ↑ ⊥))))) 
       → Void
     lem (↓L () ωh x Sp)
     lem (⊃R (L <> (↓L <> ≺*≡ Z (⊃L (◇R () (↓L <> ≺*≡ Z _)) _))))
     lem (⊃R (L <> (↓L <> (≺*+ y) Z (⊃L (◇R () (↓L <> ≺*≡ Z _)) _))))
     lem (⊃R (L <> (↓L <> _ Z (⊃L (◇R βγ (↓L _ (≺*+ (≺+0 ())) Z _)) _))))
     lem (⊃R (L <> (↓L <> _ Z (⊃L (◇R βγ (↓L _ (≺*+ (≺+S () _)) Z _)) _))))
     lem (⊃R (L <> (↓L <> _ Z (⊃L (◇R βγ (↓L _ _ (S ()) _)) _))))
     lem (⊃R (L <> (↓L <> _ Z (⊃L (◇R βγ (↑R (pR (S ())))) _))))
     lem (⊃R (L <> (↓L <> _ (S ()) Sp)))
     lem (⊃R (L <> (↑R (□R N₁)))) with N₁ βγ
     ... | ↓L pf⁻ (≺*+ (≺+0 ())) Z Sp
     ... | ↓L pf⁻ (≺*+ (≺+S () y')) Z Sp
     ... | ↓L pf⁻ ωh (S ()) Sp
     ... | ↑R (↓R (↓L () ωh x Sp))
     ... | ↑R (↓R (⊃R (L <> (↓L pf⁻ (≺*+ (≺+0 ())) (S Z) Sp))))
     ... | ↑R (↓R (⊃R (L <> (↓L pf⁻ (≺*+ (≺+S () y')) (S Z) Sp))))
     ... | ↑R (↓R (⊃R (L <> (↓L pf⁻ ωh (S (S ())) Sp))))
     ... | ↑R (↓R (⊃R (L <> (↑R ()))))

   ax¬□ : [] ⊢ ¬ (□ Q) ⊃ ◇ (¬ Q) [ β ] → Void
   ax¬□ D = lem (foc D) 
    where
     lem : 
       Term [] β · (Reg (↓ (□ (a "Q" ⁺) ⊃ ↑ ⊥) ⊃ ↑ (◇ (↓ (a "Q" ⁺ ⊃ ↑ ⊥)))))
       → Void
     lem (↓L () ωh x Sp)
     lem (⊃R (L <> (↓L <> ωh Z (⊃L (□R N₁) Sp₂)))) with N₁ βγ 
     ... | ↓L pf⁻ (≺*+ (≺+0 ())) Z Sp
     ... | ↓L pf⁻ (≺*+ (≺+S () y')) Z Sp
     ... | ↓L pf⁻ _ (S ()) Sp
     ... | ↑R (pR (S ()))
     lem (⊃R (L <> (↓L <> ωh (S ()) Sp)))
     lem (⊃R (L <> (↑R (◇R βγ (↓L pf⁻ (≺*+ (≺+0 ())) Z Sp)))))
     lem (⊃R (L <> (↑R (◇R βγ (↓L pf⁻ (≺*+ (≺+S () y')) Z Sp)))))
     lem (⊃R (L <> (↑R (◇R βγ (↓L pf⁻ ωh (S ()) Sp)))))
     lem (⊃R (L <> (↑R (◇R βγ (↑R (↓R (↓L () ωh x Sp)))))))
     lem (⊃R (L <> (↑R (◇R βγ (↑R (↓R (⊃R (L pf⁺ N)))))))) with N
     ... | ↓L pf⁻ (≺*+ (≺+0 ())) (S Z) Sp
     ... | ↓L pf⁻ (≺*+ (≺+S () y')) (S Z) Sp
     ... | ↓L pf⁻ ωh (S (S ())) Sp
     ... | ↑R ()
