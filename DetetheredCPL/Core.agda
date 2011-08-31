-- Constructive Provability Logic 
-- De-tethered intuitionstic variant
-- Robert J. Simmons, Bernardo Toninho

-- Propositions and their meaning, plus the core metric

-- Turning off the positivity check is necessary; there is no hope for Agda's 
-- positivity checker to work here, and only the upwards-well-foundedness of
-- the accessibility relation preserves the consistency of Agda.
{-# OPTIONS --no-positivity-check #-}

module DetetheredCPL.Core where
open import Prelude hiding (⊥)
open import Accessibility.Inductive
open import Accessibility.IndexedList

-- Types/Propositions
infixr 10 _⊃_
data Type : Set where
   a   : (N : String) → Type
   ⊥   : Type
   _⊃_ : (A B : Type) → Type
   ◇   : (A : Type) → Type
   □   : (A : Type) → Type

module CORE (UWF : UpwardsWellFounded) where 
   open TRANS-UWF UWF
   open ILIST UWF

   -- Contexts
   MCtx = IList Type

   -- Natural deduction without a metric
   infix 1 _⊢_[_]
   data _⊢_[_] (Γ : MCtx) : Type → W → Set where
      hyp : ∀{A w}
         → (x : A at w ∈ Γ)
         → Γ ⊢ A [ w ]
      ⊃I : ∀{A B w}
         → (D₁ : A at w :: Γ ⊢ B [ w ])
         → Γ ⊢ A ⊃ B [ w ]
      ⊃E : ∀{A B w}
         → (D₁ : Γ ⊢ A ⊃ B [ w ])
         → (D₂ : Γ ⊢ A [ w ])
         → Γ ⊢ B [ w ]
      ⊥E : ∀{C w wc} 
         → (ωh : wc ≺* w)
         → (D₁ : Γ ⊢ ⊥ [ w ])
         → Γ ⊢ C [ wc ] 
      ◇I : ∀{A w w'}
         → (ω : w ≺ w')
         → (D₁ : Γ ⊢ A [ w' ])
         → Γ ⊢ ◇ A [ w ]
      ◇E : ∀{A C w wc}
         → (ωh : wc ≺* w)
         → (D₁ : Γ ⊢ ◇ A [ w ])
         → (D₂ : ∀{w'} (ω : w ≺ w') (D₀ : Γ ⊢ A [ w' ]) → Γ ⊢ C [ wc ])
         → Γ ⊢ C [ wc ]
      □I : ∀{A w}
         → (D₁ : ∀{w'} (ω : w ≺ w') → Γ ⊢ A [ w' ])
         → Γ ⊢ □ A [ w ]
      □E : ∀{A C w wc}
         → (ωh : wc ≺* w)
         → (D₁ : Γ ⊢ □ A [ w ])
         → (D₂ : (D₀ : ∀{w'} (ω : w ≺ w') → Γ ⊢ A [ w' ]) → Γ ⊢ C [ wc ])
         → Γ ⊢ C [ wc ]

   -- The alternate, "more natural" □E rule is derivable
   □E-alt : ∀{Γ A C w w' wc} 
      → wc ≺* w
      → Γ ⊢ □ A [ w ]
      → w ≺ w' 
      → (Γ ⊢ A [ w' ] → Γ ⊢ C [ wc ])
      → Γ ⊢ C [ wc ] 
   □E-alt ωh D ω D' = □E ωh D (λ D'' → D' (D'' ω))


   -- Sequent calculus without a metric
   infix 1 _⇒_[_]
   data _⇒_[_] (Γ : MCtx) : Type → W → Set where
      hyp : ∀{Q w}
         → (x : a Q at w ∈ Γ)
         → Γ ⇒ a Q [ w ]
      ⊃R : ∀{A B w}
         → (D₁ : A at w :: Γ ⇒ B [ w ])
         → Γ ⇒ A ⊃ B [ w ]
      ⊃L : ∀{A B C w wc}
         → (ωh : wc ≺* w)
         → (x : (A ⊃ B) at w ∈ Γ)  
         → (D₁ : Γ ⇒ A [ w ])
         → (D₂ : B at w :: Γ ⇒ C [ wc ])
         → Γ ⇒ C [ wc ]
      ⊥L : ∀{C w wc} 
         → (ωh : wc ≺* w)
         → (x : ⊥ at w ∈ Γ)
         → Γ ⇒ C [ wc ] 
      ◇R : ∀{A w w'}
         → (ω : w ≺ w')
         → (D₁ : Γ ⇒ A [ w' ])
         → Γ ⇒ ◇ A [ w ]
      ◇L : ∀{A C w wc}
         → (ωh : wc ≺* w)
         → (x : (◇ A) at w ∈ Γ)
         → (D₁ : ∀{w'} (ω : w ≺ w') (D₀ : Γ ⇒ A [ w' ]) → Γ ⇒ C [ wc ])
         → Γ ⇒ C [ wc ]
      □R : ∀{A w}
         → (D₁ : ∀{w'} (ω : w ≺ w') → Γ ⇒ A [ w' ]) 
         → Γ ⇒ □ A [ w ]
      □L : ∀{A C w wc}
         → (ωh : wc ≺* w)
         → (x : (□ A) at w ∈ Γ)
         → (D₁ : (D₀ : ∀{w'} (ω : w ≺ w') → Γ ⇒ A [ w' ]) → Γ ⇒ C [ wc ])
         → Γ ⇒ C [ wc ]

