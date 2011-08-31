-- Constructive Provability Logic 
-- The minimal, modal, propositional fragment
-- Robert J. Simmons, Bernardo Toninho

-- Propositions and their meaning, plus the core metric

-- Turning off the positivity check is necessary; there is no hope for Agda's 
-- positivity checker to work here, and only the upwards-well-foundedness of
-- the accessibility relation preserves the consistency of Agda.
{-# OPTIONS --no-positivity-check #-}

module MinimalCPL.Core where
open import Prelude
open import Accessibility.Inductive
open import Accessibility.IndexedList

-- Types/Propositions
infixr 10 _⊃_
data Type : Set where
   a   : (N : String) → Type
   _⊃_ : (A B : Type) → Type
   ◇   : (A : Type) → Type
   □   : (A : Type) → Type
   ¬◇  : (A : Type) → Type
   ¬□  : (A : Type) → Type

module CORE (UWF : UpwardsWellFounded) where 
   open UpwardsWellFounded UWF
   open ILIST UWF

   -- Contexts
   MCtx = IList Type

   -- Natural deduction without a metric
   infix 1 _⊢_[_]
   data _⊢_[_] : MCtx → Type → W → Set where
      hyp : ∀{A Γ w}
         → A at w ∈ Γ
         → Γ ⊢ A [ w ]
      ⊃I : ∀{Γ A B w}
         → A at w :: Γ ⊢ B [ w ]
         → Γ ⊢ A ⊃ B [ w ]
      ⊃E : ∀{Γ A B w}
         → Γ ⊢ A ⊃ B [ w ]
         → Γ ⊢ A [ w ]
         → Γ ⊢ B [ w ]
      ◇I : ∀{Γ A w w'}
         → w ≺ w'
         → Γ ⊢ A [ w' ]
         → Γ ⊢ ◇ A [ w ]
      ◇E : ∀{Γ A C w}
         → Γ ⊢ ◇ A [ w ] 
         → (∀{w'} → w ≺ w' → Γ ⊢ A [ w' ] → Γ ⊢ C [ w ])
         → Γ ⊢ C [ w ]
      □I : ∀{Γ A w}
         → (∀{w'} → w ≺ w' → Γ ⊢ A [ w' ])
         → Γ ⊢ □ A [ w ]
      □E : ∀{Γ A C w}
         → Γ ⊢ □ A [ w ]
         → ((∀{w'} → w ≺ w' → Γ ⊢ A [ w' ]) → Γ ⊢ C [ w ])
         → Γ ⊢ C [ w ]
      ¬◇I : ∀{Γ A w}
         → (∀{w'} → w ≺ w' → Γ ⊢ A [ w' ] → Void)
         → Γ ⊢ ¬◇ A [ w ]
      ¬◇E : ∀{Γ A C w}
         → Γ ⊢ ¬◇ A [ w ]
         → ((∀{w'} → w ≺ w' → Γ ⊢ A [ w' ] → Void) → Γ ⊢ C [ w ])
         → Γ ⊢ C [ w ]
      ¬□I : ∀{Γ A w w'}
         → w ≺ w'
         → (Γ ⊢ A [ w' ] → Void)
         → Γ ⊢ ¬□ A [ w ]
      ¬□E : ∀{Γ A C w}
         → Γ ⊢ ¬□ A [ w ] 
         → (∀{w'} → w ≺ w' → (Γ ⊢ A [ w' ] → Void) → Γ ⊢ C [ w ])
         → Γ ⊢ C [ w ]

   -- The alternate, "more natural" □E rule is derivable
   □E-alt : ∀{Γ A C w w'} 
      → Γ ⊢ □ A [ w ]
      → w ≺ w' 
      → (Γ ⊢ A [ w' ] → Γ ⊢ C [ w ])
      → Γ ⊢ C [ w ] 
   □E-alt D ω D' = □E D (λ D'' → D' (D'' ω))

   -- Sequent calculus without a metric
   infix 1 _⇒_[_]
   data _⇒_[_] : MCtx → Type → W → Set where
      hyp : ∀{Q Γ w}
         → a Q at w ∈ Γ
         → Γ ⇒ a Q [ w ]
      ⊃R : ∀{Γ A B w}
         → A at w :: Γ ⇒ B [ w ]
         → Γ ⇒ A ⊃ B [ w ]
      ⊃L : ∀{Γ A B C w}
         → (A ⊃ B) at w ∈ Γ  
         → Γ ⇒ A [ w ]
         → B at w :: Γ ⇒ C [ w ]
         → Γ ⇒ C [ w ]
      ◇R : ∀{Γ A w w'}
         → w ≺ w'
         → Γ ⇒ A [ w' ]
         → Γ ⇒ ◇ A [ w ]
      ◇L : ∀{Γ A C w}
         → (◇ A) at w ∈ Γ
         → (∀{w'} → w ≺ w' → Γ ⇒ A [ w' ] → Γ ⇒ C [ w ])
         → Γ ⇒ C [ w ]
      □R : ∀{Γ A w}
         → (∀{w'} → w ≺ w' → Γ ⇒ A [ w' ]) 
         → Γ ⇒ □ A [ w ]
      □L : ∀{Γ A C w}
         → (□ A) at w ∈ Γ
         → ((∀{w'} → w ≺ w' → Γ ⇒ A [ w' ]) → Γ ⇒ C [ w ])
         → Γ ⇒ C [ w ]
      ¬◇R : ∀{Γ A w}
         → (∀{w'} → w ≺ w' → Γ ⇒ A [ w' ] → Void)
         → Γ ⇒ ¬◇ A [ w ]
      ¬◇L : ∀{Γ A C w}
         → (¬◇ A) at w ∈ Γ
         → ((∀{w'} → w ≺ w' → Γ ⇒ A [ w' ] → Void) → Γ ⇒ C [ w ])
         → Γ ⇒ C [ w ]
      ¬□R : ∀{Γ A w w'}
         → w ≺ w'
         → (Γ ⇒ A [ w' ] → Void)
         → Γ ⇒ ¬□ A [ w ] 
      ¬□L : ∀{Γ A w C}
         → (¬□ A) at w ∈ Γ
         → (∀{w'} → w ≺ w' → (Γ ⇒ A [ w' ] → Void) → Γ ⇒ C [ w ])
         → Γ ⇒ C [ w ]

   -- Core metric
   -- The metric could be split, one for the sequent calculus and one for the 
   -- natural deduction system, but there's no real reason to do so
   data Shape (Δ : MCtx) (w : W) : Set where
      s0 : Shape Δ w
      s1 : Shape Δ w → Shape Δ w
      s2 : Shape Δ w → Shape Δ w → Shape Δ w 
      s3 : Shape Δ w → Shape Δ w → Shape Δ w → Shape Δ w
      s◇⇒ : ∀{A}
          → (∀{w'} → w ≺ w' → Δ ⇒ A [ w' ] → Shape Δ w) → Shape Δ w
      s◇⊢ : ∀{A} 
          → (∀{w'} → w ≺ w' → Δ ⊢ A [ w' ] → Shape Δ w) → Shape Δ w
      s□⇒ : ∀{A} 
          → ((∀{w'} → w ≺ w' → Δ ⇒ A [ w' ]) → Shape Δ w) → Shape Δ w
      s□⊢ : ∀{A} 
          → ((∀{w'} → w ≺ w' → Δ ⊢ A [ w' ]) → Shape Δ w) → Shape Δ w
      s¬◇⇒ : ∀{A} 
          → ((∀{w'} → w ≺ w' → Δ ⇒ A [ w' ] → Void) → Shape Δ w) → Shape Δ w
      s¬◇⊢ : ∀{A} 
          → ((∀{w'} → w ≺ w' → Δ ⊢ A [ w' ] → Void) → Shape Δ w) → Shape Δ w
      s¬□⇒ : ∀{A} 
          → (∀{w'} → w ≺ w' → (Δ ⇒ A [ w' ] → Void) → Shape Δ w) → Shape Δ w
      s¬□⊢ : ∀{A} 
          → (∀{w'} → w ≺ w' → (Δ ⊢ A [ w' ] → Void) → Shape Δ w) → Shape Δ w
