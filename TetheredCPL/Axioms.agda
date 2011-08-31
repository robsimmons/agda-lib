-- Constructive Provability Logic 
-- Tethered intuitionstic variant
-- Robert J. Simmons, Bernardo Toninho

-- Valid and invalid axioms

module TetheredCPL.Axioms where
open import Prelude hiding (⊥ ; ¬)
open import Accessibility.Inductive
open import Accessibility.Three
open import Accessibility.IndexedList
open import TetheredCPL.Core
open import TetheredCPL.NatDeduction
open import TetheredCPL.Sequent
open import TetheredCPL.Equiv

¬ : Type → Type
¬ A = A ⊃ ⊥

module PROPERTIES (UWF : UpwardsWellFounded) where
   open TRANS-UWF UWF
   open CORE UWF 

   Trans : Set
   Trans = ∀{w₁ w₂ w₃} → w₁ ≺ w₂ → w₂ ≺ w₃ → w₁ ≺ w₃

   Con : MCtx → W → Set
   Con Γ w = ∀ {w'} → w ≺ w' → Γ ⊢ ⊥ [ w' ] → Void

module AXIOMS (UWF : UpwardsWellFounded) where
   open TRANS-UWF UWF
   open PROPERTIES UWF
   open ILIST UWF
   open CORE UWF 
   open EQUIV UWF

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
   ax⊥E = ⊃I (⊥E (hyp Z))

 -- Necessitation rule (Theorem 3.2)
   Nec : ∀{Γ A} 
      → (∀{w} → Γ ⊢ A [ w ])
      → (∀{w} → Γ ⊢ □ A [ w ])
   Nec D = □I (λ ω → D) 

 -- Axioms of IK, Simpson's intuitionistic modal logic (Theorem 3.3)
   axK□ : ∀{Γ A B w}
      → Γ ⊢ □ (A ⊃ B) ⊃ □ A ⊃ □ B [ w ]
   axK□ = ⊃I (⊃I (□E (hyp (S Z))
      λ DAB → □E (hyp Z) 
      λ DA → □I (λ ω → ⊃E (DAB ω) (DA ω))))

   axK◇ : ∀{Γ A B w}
      → Γ ⊢ □ (A ⊃ B) ⊃ ◇ A ⊃ ◇ B [ w ]
   axK◇ = ⊃I (⊃I (□E (hyp (S Z)) 
      λ DAB → ◇E (hyp Z) 
      λ ω DA → ◇I ω (⊃E (DAB ω) DA)))

   ax4□ : ∀{Γ A w}
      → Trans
      → Γ ⊢ □ A ⊃ □ (□ A) [ w ]
   ax4□ _≺≺_ = ⊃I (□E (hyp Z) 
      λ D → □I λ ω → □I λ ω' → D (ω ≺≺ ω'))

 -- Axiom GL (Theorem 3.4)
   axGL : ∀{Γ A w}
      → Trans
      → Γ ⊢ □ (□ A ⊃ A) ⊃ □ A [ w ]
   axGL {A = A} _≺≺_ = ind P lemma _
    where
      P : W → Set
      P = λ w → ∀{Γ} → Γ ⊢ □ (□ A ⊃ A) ⊃ □ A [ w ]
   
      lemma : (w : W) → ((w' : W) → w ≺ w' → P w') → P w
      lemma w ih = ⊃I (□E (hyp Z) 
         λ DInd → □I 
         λ ω → ⊃E (DInd ω) (⊃E (ih _ ω) (□I (λ ω' → DInd (ω ≺≺ ω')))))

 -- Löb rule (Theorem 3.5)
   Löb : ∀{Γ A}
      → (∀{w} → Γ ⊢ □ A ⊃ A [ w ])
      → (∀{w} → Γ ⊢ A [ w ])
   Löb {Γ = Γ} {A = A} = λ D {w} → ind P lemma _ D
    where
      P : W → Set
      P = λ w → (∀{w} → Γ ⊢ □ A ⊃ A [ w ]) → Γ ⊢ A [ w ]
 
      lemma : (w : W) → ((w' : W) → w ≺ w' → P w') → P w
      lemma w ih D = ⊃E D (□I (λ ω → ih _ ω D)) 

 -- De Morgan laws (Theorem 3.6)
   ax◇¬ : ∀{Γ A w} 
      → Con Γ w 
      → Γ ⊢ ◇ (¬ A) ⊃ ¬ (□ A) [ w ]
   ax◇¬ con = ⊃I (◇E (hyp Z) 
      λ ω D₀ → ⊃I (□E (hyp Z) 
      λ D₁ → abort (con ω (wk-nd (wkto ω) (⊃E D₀ (wk-nd (wkto ω) (D₁ ω)))))))

   ax□¬ : ∀{Γ A w} 
      → Con Γ w 
      → Γ ⊢ □ (¬ A) ⊃ ¬ (◇ A) [ w ]
   ax□¬ con = ⊃I (□E (hyp Z)
      λ D₀ → ⊃I (◇E (hyp Z)
      λ ω D₁ → 
       abort (con ω (wk-nd (wkto ω) (⊃E (D₀ ω) (wk-nd (wkto ω) D₁))))))
    
module NON-AXIOMS where
   open TRANS-UWF SmallExample
   open PROPERTIES SmallExample
   open ILIST SmallExample
   open CORE SmallExample
   open SEQUENT SmallExample
   open EQUIV SmallExample

   Q : Type
   Q = a "Q"   

 -- Axioms of IK, Simpson's intuitionistic modal logic (Theorem 3.3)
   ax◇⊥ : [ ⊥ at γ ] ⇒ ¬ (◇ ⊥) [ β ] → Void
   ax◇⊥ (⊃L (S ()) _ _) 
   ax◇⊥ (⊥L (S ())) 
   ax◇⊥ (◇L (S ()) _)
   ax◇⊥ (□L (S ()) _) 
   ax◇⊥ (⊃R D) = lem1 D
    where
      lem1 : ◇ ⊥ at β :: ⊥ at γ :: [] ⇒ ⊥ [ β ] → Void 
      lem1 (□L (S (S ())) _) 
      lem1 (⊃L (S (S ())) _ _)
      lem1 (⊥L (S (S ())))
      lem1 (◇L (S (S ())) _)
      lem1 (◇L Z D) = lem1 (D βγ (⊥L (S Z)))

   axIK : [] ⇒ (◇ Q ⊃ □ ⊥) ⊃ □ (Q ⊃ ⊥) [ β ] → Void
   axIK (⊃R (⊃L (S ()) D₁ D₂))
   axIK (⊃R (⊥L (S ())))
   axIK (⊃R (◇L (S ()) D₁))
   axIK (⊃R (□L (S ()) D₁))
   axIK (⊃L () D₁ D₂)
   axIK (⊥L ())
   axIK (◇L () D₁) 
   axIK (□L () D₁)
   axIK (⊃R (⊃L Z D₁ D₂)) = lem1 D₁
    where
      lem2 : ((◇ Q ⊃ □ ⊥) at β :: []) ⇒ Q [ γ ] → Void
      lem2 (hyp (S ()))
      lem2 (⊃L (S ()) D₁' D₂)
      lem2 (⊥L (S ()))
      lem2 (◇L (S ()) D₁')
      lem2 (□L (S ()) D₁') 
     
      lem1 : ((◇ Q) ⊃ □ ⊥) at β :: [] ⇒ (◇ Q) [ β ] → Void
      lem1 (⊃L Z D₁' D₂) = lem1 D₁'
      lem1 (⊃L (S ()) D₁' D₂)
      lem1 (⊥L (S ())) 
      lem1 (◇R βγ D₁') = lem2 D₁'
      lem1 (◇L (S ()) D₁')
      lem1 (□L (S ()) D₁') 

   axIK (⊃R (□R D)) = lem1 (D βγ)
    where
      lem2 : (Q at γ :: (◇ Q ⊃ □ ⊥) at β :: []) ⇒ ⊥ [ γ ] → Void
      lem2 (⊃L (S (S ())) _ _)
      lem2 (⊥L (S (S ())))
      lem2 (◇L (S (S ())) _)
      lem2 (□L (S (S ())) _) 

      lem1 : ((◇ Q ⊃ □ ⊥) at β :: []) ⇒ (Q ⊃ ⊥) [ γ ] → Void
      lem1 (⊃R D₁) = lem2 D₁
      lem1 (⊃L (S ()) D₁ D₂)
      lem1 (⊥L (S ()))
      lem1 (◇L (S ()) D₁)
      lem1 (□L (S ()) D₁)

 -- De Morgan laws (Theorem 3.6)
   ax◇¬ : [ ⊥ at γ ] ⇒ ◇ (¬ Q) ⊃ ¬ (□ Q) [ β ] → Void
   ax◇¬ (⊃L (S ()) _ _)
   ax◇¬ (⊥L (S ())) 
   ax◇¬ (◇L (S ()) _)
   ax◇¬ (□L (S ()) _)
   ax◇¬ (⊃R D) = lem1 D
    where
     mutual
      lem1 : ◇ (¬ Q) at β :: ⊥ at γ :: [] ⇒ ¬ (□ Q) [ β ] → Void
      lem1 (⊃L (S (S ())) _ _)
      lem1 (⊥L (S (S ()))) 
      lem1 (◇L (S (S ())) _)
      lem1 (□L (S (S ())) _)
      lem1 (◇L Z D) = lem1 (D βγ (⊃R (⊥L (S (S Z)))))
      lem1 (⊃R D) = lem2 D
 
      lem2 : □ Q at β :: ◇ (¬ Q) at β :: ⊥ at γ :: [] ⇒ ⊥ [ β ] → Void
      lem2 (⊃L (S (S (S ()))) _ _)
      lem2 (⊥L (S (S (S ())))) 
      lem2 (◇L (S (S (S ()))) _)
      lem2 (□L (S (S (S ()))) _)
      lem2 (□L Z D) = lem2 (D lem3)
      lem2 (◇L (S Z) D) = lem2 (D βγ (⊥L (S (S Z))))

      lem3 : ∀{w'} → β ≺ w' 
         → □ Q at β :: ◇ (¬ Q) at β :: ⊥ at γ :: [] ⇒ Q [ w' ] 
      lem3 βγ = ⊥L (S (S Z))
 
   ax□¬ : [ ⊥ at γ ] ⇒ □ (¬ Q) ⊃ ¬ (◇ Q) [ β ] → Void
   ax□¬ (⊃L (S ()) _ _)
   ax□¬ (⊥L (S ())) 
   ax□¬ (◇L (S ()) _)
   ax□¬ (□L (S ()) _)
   ax□¬ (⊃R D) = lem1 D
    where
     mutual
      lem1 : □ (¬ Q) at β :: ⊥ at γ :: [] ⇒ ¬ (◇ Q) [ β ] → Void
      lem1 (⊃L (S (S ())) _ _)
      lem1 (⊥L (S (S ()))) 
      lem1 (◇L (S (S ())) _)
      lem1 (□L (S (S ())) _)
      lem1 (□L Z D) = lem1 (D (λ ω → lem3 ω (S Z)))
      lem1 (⊃R D) = lem2 D

      lem2 : ◇ Q at β :: □ (¬ Q) at β :: ⊥ at γ :: [] ⇒ ⊥ [ β ] → Void
      lem2 (⊃L (S (S (S ()))) _ _)
      lem2 (⊥L (S (S (S ())))) 
      lem2 (◇L (S (S (S ()))) _)
      lem2 (□L (S (S (S ()))) _)
      lem2 (◇L Z D) = lem2 (D βγ (⊥L (S (S Z))))
      lem2 (□L (S Z) D) = lem2 (D (λ ω → lem3 ω (S (S Z))))

      lem3 : ∀{Γ A w'} → β ≺ w' → ⊥ at γ ∈ Γ → Γ ⇒ A [ w' ]
      lem3 βγ x = ⊥L x

   ax¬◇ : [ Q at β ] ⇒ ¬ (◇ Q) ⊃ □ (¬ Q) [ β ] → Void
   ax¬◇ (⊃R (⊃L (S (S ())) D₁ D₂))
   ax¬◇ (⊃R (⊥L (S (S ()))))
   ax¬◇ (⊃R (◇L (S (S ())) D₁))
   ax¬◇ (⊃R (□L (S (S ())) D₁))
   ax¬◇ (⊃L (S ()) D₁ D₂) 
   ax¬◇ (⊥L (S ()))
   ax¬◇ (◇L (S ()) D₁) 
   ax¬◇ (□L (S ()) D₁) 
   ax¬◇ (⊃R (□R D₁)) = lem (D₁ βγ)
    where
      lem : (◇ Q ⊃ ⊥) at β :: Q at β :: [] ⇒ Q ⊃ ⊥ [ γ ] → Void
      lem (⊃R (⊃L (S (S (S ()))) D₁ D₂))
      lem (⊃R (⊥L (S (S (S ())))))
      lem (⊃R (◇L (S (S (S ()))) D₁))
      lem (⊃R (□L (S (S (S ()))) D₁))
      lem (⊃L (S (S ())) D₁ D₂)
      lem (⊥L (S (S ())))
      lem (◇L (S (S ())) D₁)
      lem (□L (S (S ())) D₁)

   ax¬◇ (⊃R (⊃L Z D₁ D₂)) = lem D₁
    where
      lem : ¬ (◇ Q) at β :: Q at β :: [] ⇒ ◇ Q [ β ] → Void
      lem (⊃L Z D₁ D₂) = lem D₁
      lem (⊃L (S (S ())) D₁ D₂)
      lem (⊥L (S (S ())))
      lem (◇R βγ (hyp (S (S ())))) 
      lem (◇R βγ (⊃L (S (S ())) D₁ D₂))
      lem (◇R βγ (⊥L (S (S ())))) 
      lem (◇R βγ (◇L (S (S ())) D₁)) 
      lem (◇R βγ (□L (S (S ())) D₁)) 
      lem (◇L (S (S ())) D₁)
      lem (□L (S (S ())) D₁) 

   ax¬□ : [] ⇒ ¬ (□ Q) ⊃ ◇ (¬ Q) [ β ] → Void
   ax¬□ (⊃R (⊃L (S ()) _ _))
   ax¬□ (⊃R (⊥L (S ())))
   ax¬□ (⊃R (◇R βγ (⊃R (⊃L (S (S ())) _ _))))
   ax¬□ (⊃R (◇R βγ (⊃R (⊥L (S (S ()))))))
   ax¬□ (⊃R (◇R βγ (⊃R (◇L (S (S ())) _))))
   ax¬□ (⊃R (◇R βγ (⊃R (□L (S (S ())) _))))
   ax¬□ (⊃R (◇R βγ (⊃L (S ()) _ _)))
   ax¬□ (⊃R (◇R βγ (⊥L (S ()))))
   ax¬□ (⊃R (◇R βγ (◇L (S ()) _)))
   ax¬□ (⊃R (◇R βγ (□L (S ()) _)))
   ax¬□ (⊃R (◇L (S ()) _))
   ax¬□ (⊃R (□L (S ()) _))
   ax¬□ (⊃L () _ _)
   ax¬□ (⊥L ())
   ax¬□ (◇L () _)
   ax¬□ (□L () _)
   ax¬□ (⊃R (⊃L Z D₁ _)) = lem1 D₁ -- lem1 D₁
    where
      lem2 : (¬ (□ Q) at β :: []) ⇒ Q [ γ ] → Void
      lem2 (hyp (S ())) 
      lem2 (⊃L (S ()) _ _)
      lem2 (⊥L (S ()))
      lem2 (◇L (S ()) _)
      lem2 (□L (S ()) _) 

      lem1 : ¬ (□ Q) at β :: [] ⇒ □ Q [ β ] → Void
      lem1 (⊃L Z D₁ _) = lem1 D₁
      lem1 (⊃L (S ()) _ _)
      lem1 (⊥L (S ()))
      lem1 (◇L (S ()) _)
      lem1 (□R D₁) = lem2 (D₁ βγ)
      lem1 (□L (S ()) _)

