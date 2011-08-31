-- Constructive Provability Logic 
-- Tethered intuitionstic variant
-- Robert J. Simmons, Bernardo Toninho

-- Equivalence of sequent calculus and natural deduction

module TetheredCPL.Equiv where
open import Prelude
open import Accessibility.Inductive
open import Accessibility.IndexedList
open import TetheredCPL.Core
open import TetheredCPL.NatDeduction
open import TetheredCPL.Sequent

module EQUIV (UWF : UpwardsWellFounded) where
   open TRANS-UWF UWF
   open ILIST UWF
   open CORE UWF
   open NAT-DEDUCTION UWF
   open SEQUENT UWF

   -- Name conflict between natural deduction and sequent calculus weakening
   wk-nd : ∀ {Γ Δ A w} → Γ ⊆ Δ to w → Γ ⊢ A [ w ] → Δ ⊢ A [ w ] 
   wk-nd = NAT-DEDUCTION.wk UWF

   wk-seq : ∀ {Γ Δ A w} → Γ ⊆ Δ to w → Γ ⇒ A [ w ] → Δ ⇒ A [ w ] 
   wk-seq = SEQUENT.wk UWF

   -- Equivalence of natural deduction and sequent calculus
   -- Things are set up such that we have to prove both at once
   equivP : W → Set
   equivP = λ w → 
      ((∀{Γ A} → Γ ⊢ A [ w ] → Γ ⇒ A [ w ]) 
      × (∀{Γ A} → Γ ⇒ A [ w ] → Γ ⊢ A [ w ]))

   -- Given the induction hypothesis, natural deduction implies sequent
   nd→seq' : (w : W) → ((w' : W) → w ≺ w' → equivP w')
              → ∀{Γ A} → Γ ⊢ A [ w ] → Γ ⇒ A [ w ]
   nd→seq' w ih (hyp iN) = iden' _ iN
   nd→seq' w ih (⊃I D) = ⊃R (nd→seq' w ih D)
   nd→seq' w ih (⊃E D D') = 
      cut (nd→seq' w ih D')
       (cut (wk-seq wken (nd→seq' w ih D))
        (⊃L Z (iden' _ (S Z)) (iden _)))
   nd→seq' w ih (⊥E D) = cut (nd→seq' w ih D) (⊥L Z)
   nd→seq' w ih (◇I ω D) = ◇R ω (fst (ih _ ω) D)
   nd→seq' w ih (◇E D D') = 
      cut (nd→seq' w ih D) 
       (◇L Z (λ ω D₀ → wk-seq wken (nd→seq' w ih 
        (D' ω (snd (ih _ ω) (wk-seq (wkto ω) D₀))))))
   nd→seq' w ih (□I D) = □R (λ ω → fst (ih _ ω) (D ω))
   nd→seq' w ih (□E D D') = 
      cut (nd→seq' w ih D)
       (□L Z (λ D₀ → wk-seq wken (nd→seq' w ih 
        (D' (λ ω → snd (ih _ ω) (wk-seq (wkto ω) (D₀ ω)))))))

   -- Given the induction hypothesis, sequent implies natural deduction
   seq→nd' : (w : W) → ((w' : W) → w ≺ w' → equivP w')
              → ∀{Γ A} → Γ ⇒ A [ w ] → Γ ⊢ A [ w ]
   seq→nd' w ih (hyp iN) = hyp iN
   seq→nd' w ih (⊃R D) = ⊃I (seq→nd' w ih D)
   seq→nd' w ih (⊃L iN D D') = 
      subst (⊃E (hyp iN) (seq→nd' w ih D)) (seq→nd' w ih D')
   seq→nd' w ih (⊥L iN) = ⊥E (hyp iN)
   seq→nd' w ih (◇R ω D) = ◇I ω (snd (ih _ ω) D)
   seq→nd' w ih (◇L iN D) = 
      ◇E (hyp iN) (λ ω D₀ → seq→nd' w ih (D ω (fst (ih _ ω) D₀)))
   seq→nd' w ih (□R D) = □I (λ ω → snd (ih _ ω) (D ω))
   seq→nd' w ih (□L iN D) = 
      □E (hyp iN) (λ D₀ → seq→nd' w ih (D (λ ω → fst (ih _ ω) (D₀ ω))))

   -- Therefore, both sequent calculus and natural deduction are equivalent
   nd⇆seq : (w : W) → 
      ((∀{Γ A} → Γ ⊢ A [ w ] → Γ ⇒ A [ w ]) 
      × (∀{Γ A} → Γ ⇒ A [ w ] → Γ ⊢ A [ w ]))
   nd⇆seq = 
      ind equivP (λ w ih → (λ D → nd→seq' _ ih D) , (λ D → seq→nd' _ ih D))
  
   nd→seq : ∀{Γ A w} → Γ ⊢ A [ w ] → Γ ⇒ A [ w ]
   nd→seq = fst (nd⇆seq _)

   seq→nd : ∀{Γ A w} → Γ ⇒ A [ w ] → Γ ⊢ A [ w ]
   seq→nd = snd (nd⇆seq _)
