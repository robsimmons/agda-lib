-- Constructive Provability Logic 
-- The minimal, modal, propositional fragment
-- Robert J. Simmons, Bernardo Toninho

-- Valid and invalid axioms

module MinimalCPL.Axioms where
open import Prelude
open import Accessibility.Inductive
open import Accessibility.IndexedList
open import MinimalCPL.Core
open import MinimalCPL.Sequent
open import MinimalCPL.Equiv

Ctx = List Type

data Axiom : Type → Set where
   -- Intuitionstic, propositional logic
   K : ∀{A B} → Axiom (A ⊃ B ⊃ A)
   □K : ∀{A B} → Axiom (□ (A ⊃ B) ⊃ □ A ⊃ □ B)
   ◇K : ∀{A B} → Axiom (□ (A ⊃ B) ⊃ ◇ A ⊃ ◇ B)
   ¬□K : ∀{A B} → Axiom (□ (A ⊃ B) ⊃ ¬□ B ⊃ ¬□ A)
   ¬◇K : ∀{A B} → Axiom (□ (A ⊃ B) ⊃ ¬◇ B ⊃ ¬◇ A)
   □N : ∀{A B} → Axiom (¬□ A ⊃ □ A ⊃ B)
   ◇N : ∀{A B} → Axiom (¬◇ A ⊃ ◇ A ⊃ B)
   □C : ∀{A B} → Axiom (□ A ⊃ ¬◇ (A ⊃ B))
   ◇C : ∀{A B} → Axiom (◇ A ⊃ ¬□ (A ⊃ B))

data TransAxiom : Type → Set where
   □4 : ∀{A} → TransAxiom (□ A ⊃ □ (□ A))

data Hilbert : Bool → Ctx → Type → Set where
   


mutual
   infix 4 _⊩_
   infix 4 _⊪_

   _⊩_ : Ctx → Type → Set
   Γ ⊩ A = Hil False Γ A

   _⊪_ : Ctx → Type → Set
   Γ ⊪ A = Hil True Γ A

   data Hil : Bool → Ctx → Type → Set where
      hyp : ∀{b Γ A} → A ∈ Γ → Hil b Γ A
      4□ : ∀{Γ A} → Γ ⊪ (□ A)

module AXIOMS (UWF : UpwardsWellFounded) where
   open TRANS-UWF UWF
   open ILIST UWF
   open CORE UWF 
   open SEQUENT UWF

   Trans : Set
   Trans = ∀{w₁ w₂ w₃} → w₁ ≺ w₂ → w₂ ≺ w₃ → w₁ ≺ w₃

   infix 4 ⊩_
   ⊩_ : Type → Set
   ⊩ A = ∀{Γ w} → Γ ⊢ A [ w ]

   -- Intuitionstic modal logic
   MP : ∀{A B} → ⊩ A ⊃ B → ⊩ A → ⊩ B
   MP DAB DA = ⊃E DAB DA

   axI : ∀{A} → ⊩ A ⊃ A 
   axI = ⊃I (hyp Z)

   axS : ∀{A B} → ⊩ A ⊃ B ⊃ A 
   axS = ⊃I (⊃I (hyp (S Z)))

   axK : ∀{A B C} → ⊩ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ (A ⊃ C) 
   axK = ⊃I (⊃I (⊃I (⊃E (⊃E (hyp (S (S Z))) (hyp Z)) (⊃E (hyp (S Z)) (hyp Z)))))

   -- Modal logic
   Nec : ∀{A} → ⊩ A → ⊩ □ A
   Nec D = □I (λ ω → D)

   ax□ : ∀{A B} → ⊩ □ (A ⊃ B) ⊃ (□ A ⊃ □ B)
   ax□ = ⊃I (⊃I (□E (hyp (S Z))
      λ DAB → □E (hyp Z) 
      λ DA → □I (λ ω → ⊃E (DAB ω) (DA ω))))
   
   axK◇ : ∀{A B} → ⊩ □ (A ⊃ B) ⊃ (◇ A ⊃ ◇ B) 
   axK◇ = ⊃I (⊃I (□E (hyp (S Z)) 
      λ DAB → ◇E (hyp Z) 
      λ ω DA → ◇I ω (⊃E (DAB ω) DA)))

   ax4□ : ∀{A} → Trans →  ⊩ □ A ⊃ □ (□ A)
   ax4□ _≺≺_ = ⊃I (□E (hyp Z) λ D → □I (λ ω → □I (λ ω' → D (ω ≺≺ ω'))))

   ax4◇ : ∀{A} → Trans →  ⊩ ◇ (◇ A) ⊃ ◇ A
   ax4◇ _≺≺_ = ⊃I (◇E (hyp Z) (λ ω D → ◇I ω {!!}))

   -- Negated modal connectives
   axN□ : ∀{A B} → ⊩ ¬□ A ⊃ □ A ⊃ B 
   axN□ = ⊃I (⊃I (□E (hyp Z) 
      λ DA → ¬□E (hyp (S Z)) 
      λ ω ¬DA → abort (¬DA (DA ω))))

   axN◇ : ∀{A B} → ⊩ ¬◇ A ⊃ ◇ A ⊃ B 
   axN◇ = ⊃I (⊃I (◇E (hyp Z)
      λ ω DA → ¬◇E (hyp (S Z))
      λ ¬DA → abort (¬DA ω DA)))

   -- Provability logic
   LöbP : W → Set
   LöbP = λ w → ∀{Γ A} → ⊩ □ A ⊃ A → Γ ⊢ A [ w ]

   Löb' : (w : W) → ((w' : W) → w ≺ w' → LöbP w') → LöbP w
   Löb' w ih D = ⊃E D (□I (λ ω → ih _ ω D))

   Löb : ∀{A} → ⊩ □ A ⊃ A → ⊩ A
   Löb D = ind LöbP Löb' _ D

   axGLP : W → Set
   axGLP = λ w → ∀{Γ A} → Trans → Γ ⊢ □ (□ A ⊃ A) ⊃ □ A [ w ]
   
   axGL' : (w : W) → ((w' : W) → w ≺ w' → axGLP w') → axGLP w
   axGL' w ih _≺≺_ = ⊃I (□E (hyp Z) 
      λ DInd → □I 
      λ ω → ⊃E (DInd ω) (⊃E (ih _ ω _≺≺_) (□I (λ ω' → DInd (ω ≺≺ ω')))))

   axGL : ∀{A} → Trans → ⊩ □ (□ A ⊃ A) ⊃ □ A 
   axGL _≺≺_ = ind axGLP axGL' _ _≺≺_

module COUNTERMODELS where
   open import Accessibility.Nat

   infix 4 ⊮_
   ⊮_ : Type → Set₁
   ⊮ A = ∃ λ UWF → ∃ λ Γ → ∃ λ w → CORE._⊢_[_] UWF Γ A w → Void

   -- ax◇C1 : ⊩ ◇ A ⊃ ((□ (A ⊃ ⊥)) ⊃ ⊥)
   -- ax◇C2 : ⊩ ((□ (A ⊃ ⊥)) ⊃ ⊥) ⊃ ◇ A 
   -- ¬axD : ⊮ ◇ ⊤
   -- ¬axT□ : ⊮ □ A ⊃ A
   -- ¬axT◇ : ⊮ A ⊃ ◇ A
   -- ¬axB◇ : ⊮ ◇ (□ A) ⊃ A
   -- ¬axB□ : ⊮ A ⊃ □ (◇ A)
   -- ¬ax4□ : ⊮ □ A ⊃ □ (□ A) -- DONE
   -- ¬ax4◇ : ⊮ ◇ (◇ A) ⊃ ◇ A -- DONE
   -- ¬ax5□ : ⊮ ◇ (□ A) ⊃ □ A
   -- ¬ax5◇ : ⊮ ◇ A ⊃ □ (◇ A) 
   -- ¬ax2 : ⊮ ◇ (□ A) ⊃ □ (◇ A) 
   -- ¬axWJ3 : ⊮ ◇ ⊥ ⊃ ⊥
   -- ¬axSW : ⊮ (◇ A ⊃ □ B) ⊃ □ (A ⊃ B)

   Q₁ = a "q1"

   ¬ax4 : ⊮ □ Q₁ ⊃ □ (□ Q₁)
   ¬ax4 = Count , [ Q₁ at 1 ] , 2 , λ D → counter2' (nd→seq D)
    where
      open ILIST Count
      open CORE Count
      open EQUIV Count

      counter0 : □ Q₁ at 2 :: Q₁ at 1 :: [] ⇒ Q₁ [ 0 ] → Void
      counter0 (hyp (S (S ())))
      counter0 (⊃L (S (S ())) _ _) 
      counter0 (◇L (S (S ())) _) 
      counter0 (□L (S (S ())) _) 
      counter0 (¬◇L (S (S ())) _)
      counter0 (¬□L (S (S ())) _)

      counter1 : □ Q₁ at 2 :: Q₁ at 1 :: [] ⇒ □ Q₁ [ 1 ] → Void
      counter1 (□R D) = counter0 (D refl)
      counter1 (⊃L (S (S ())) _ _) 
      counter1 (◇L (S (S ())) _) 
      counter1 (□L (S (S ())) _) 
      counter1 (¬◇L (S (S ())) _)
      counter1 (¬□L (S (S ())) _)

      counter2 : □ Q₁ at 2 :: Q₁ at 1 :: [] ⇒ □ (□ Q₁) [ 2 ] → Void
      counter2 (□R D) = counter1 (D refl)
      counter2 (□L Z D) = 
         counter2 
          (D (λ eq → 
           coe (resp (λ w → □ Q₁ at 2 :: Q₁ at 1 :: [] ⇒ Q₁ [ w ]) (symm eq))
            (hyp (S Z)))) 
      counter2 (⊃L (S (S ())) _ _) 
      counter2 (◇L (S (S ())) _) 
      counter2 (□L (S (S ())) _) 
      counter2 (¬◇L (S (S ())) _)
      counter2 (¬□L (S (S ())) _)

      counter2' : [ Q₁ at 1 ] ⇒ □ Q₁ ⊃ □ (□ Q₁) [ 2 ] → Void
      counter2' (⊃R D) = counter2 D
      counter2' (⊃L (S ()) _ _) 
      counter2' (◇L (S ()) _) 
      counter2' (□L (S ()) _) 
      counter2' (¬◇L (S ()) _)
      counter2' (¬□L (S ()) _)

   ¬ax4◇ : ⊮ ◇ Q₁ ⊃ ◇ (◇ Q₁)
   ¬ax4◇ = Count , [ Q₁ at 1 ] , 2 , λ D → counter2' (nd→seq D) 
    where
      open ILIST Count
      open CORE Count
      open EQUIV Count

      counter2 : ◇ Q₁ at 2 :: Q₁ at 1 :: [] ⇒ ◇ (◇ Q₁) [ 2 ] → Void
      counter2 (◇L Z D) = counter2 (D refl (hyp (S Z)))
      counter2 (◇R Refl (◇R Refl (hyp (S (S ())))))
      counter2 (◇R Refl (◇R Refl (⊃L (S (S ())) _ _)))
      counter2 (◇R Refl (◇R Refl (◇L (S (S ())) _)))
      counter2 (◇R Refl (◇R Refl (□L (S (S ())) _)))
      counter2 (◇R Refl (◇R Refl (¬◇L (S (S ())) _)))
      counter2 (◇R Refl (◇R Refl (¬□L (S (S ())) _)))
      counter2 (◇R Refl (⊃L (S (S ())) _ _)) 
      counter2 (◇R Refl (◇L (S (S ())) _))
      counter2 (◇R Refl (□L (S (S ())) _))
      counter2 (◇R Refl (¬◇L (S (S ())) _))
      counter2 (◇R Refl (¬□L (S (S ())) _))
      counter2 (⊃L (S (S ())) _ _) 
      counter2 (◇L (S (S ())) _) 
      counter2 (□L (S (S ())) _) 
      counter2 (¬◇L (S (S ())) _)
      counter2 (¬□L (S (S ())) _)

      counter2' : [ Q₁ at 1 ] ⇒ ◇ Q₁ ⊃ ◇ (◇ Q₁) [ 2 ] → Void
      counter2' (⊃R D) = counter2 D
      counter2' (⊃L (S ()) _ _) 
      counter2' (◇L (S ()) _) 
      counter2' (□L (S ()) _) 
      counter2' (¬◇L (S ()) _)
      counter2' (¬□L (S ()) _)


