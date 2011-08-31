-- Constructive Provability Logic 
-- The minimal, modal, propositional fragment
-- Robert J. Simmons, Bernardo Toninho

-- Illustration of why constructive probability logic demands an 
-- upwards-well-founded accessibility relation; with a trivial one-place
-- reflexive accessibility relation, the definition of constructive provability
-- logic makes the *metalogic* (Agda, in this case), inconsistent.

-- Original sin
{-# OPTIONS --no-positivity-check #-}

module Inconsistency where

open import Prelude

-- Only one world; trivial accessibility relation
W = Unit
record _≺_ (w1 w2 : Unit) : Set where
   constructor <>

data Type : Set where
   a   : (N : String) → Type
   _⊃_ : (A B : Type) → Type
   ◇   : (A : Type) → Type
 
-- Not well-founded, so we'll have to roll our own indexed lists
data Item : Set where
   _at_ : Type → W → Item 
MCtx = List Item

-- Proposed natural deduction system, simple as possible
infix 1 _⊢_[_]
data _⊢_[_] : MCtx → Type → W → Set where
   hyp : ∀{A Γ w}
      → A at w ∈ Γ
      → Γ ⊢ A [ w ]
   ◇E : ∀{Γ A C w}
      → Γ ⊢ ◇ A [ w ] 
      → (∀{w'} → w ≺ w' → Γ ⊢ A [ w' ] → Γ ⊢ C [ w ])
      → Γ ⊢ C [ w ]

-- Step one
-- Pick an atomic proposition Q, show ◇Q[w] ⊢ Q[w]
Q = a "q"
it's-true : ◇ Q at <> :: [] ⊢ Q [ <> ] 
it's-true = ◇E (hyp Z) (λ <> D → D)

-- Step two (only necessary because we're not in a sequent calculus)
-- Show that ◇Q[w] ⊢ ◇A[q] implies Q is equal to A; we can't prove much else.
only-provable-thing : ∀{A} → ◇ Q at <> :: [] ⊢ ◇ A [ <> ] → Q ≡ A 
only-provable-thing (hyp Z) = refl
only-provable-thing (hyp (S ()))
only-provable-thing (◇E y y') with only-provable-thing y
... | Refl = only-provable-thing (y' <> it's-true)

-- Step three
-- Show that there can be no proof of ◇Q[w] ⊢ Q[w] by "structural induction"
-- on our (nonpositive) inductive definition. Agda believes us because it sees
-- "D₂ <> (anything)" as a structural subterm of (◇E D₁ D₂).
it's-false : ◇ Q at <> :: [] ⊢ Q [ <> ] → Void
it's-false (hyp (S ()))
it's-false (◇E D₁ D₂) with only-provable-thing D₁
... | Refl = it's-false (D₂ <> (◇E (hyp Z) (λ <> D' → D')))

-- Step four
-- Anything you want, you've got it (ex falso quodlibet).
uh-oh : (A : Set) → A
uh-oh = abort (it's-false it's-true)

-- Just one example
0=1 : 0 ≡ 1
0=1 = uh-oh (0 ≡ 1)

3=4 : 3 ≡ 4
3=4 = NAT.s-cong (NAT.s-cong (NAT.s-cong (uh-oh (0 ≡ 1))))

2+2=5 : 2 +n 2 ≡ 5
2+2=5 = uh-oh (2 +n 2 ≡ 5)
