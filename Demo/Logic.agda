{- Basic reasoning about algebraic data types -}

module Demo.Logic where

open import Prelude

{- Units being units -}
⊤-is-a-unit-of-× : ∀{A : Set0} → ⊤ × A × ⊤ → A × ⊤ × ⊤ × ⊤ × A
⊤-is-a-unit-of-× (p1 , p2 , <>) = p2 , <> , <> , p1 , p2

{- Unit or void using the elimination forms -}
⊥-is-a-unit-of-+ : ∀{A} → A + ⊥ → A
⊥-is-a-unit-of-+ x = case x (λ x → x) (λ x → abort x)

{- Unit or void using pattern matching -}
⊥-is-impossible : {A : Set} → A + ⊥ → A
⊥-is-impossible (Inl x) = x
⊥-is-impossible (Inr ()) 

{- All units are equal -}
⊤-has-one-inhabitant : (x y : ⊤) → x ≡ y
⊤-has-one-inhabitant <> <> = Refl

⊤-is-unique : (x y : ⊤) → x ≡ y
⊤-is-unique x y = ⊤-has-one-inhabitant x x ≡≡ ⊤-has-one-inhabitant x y 

{- Sums are commutative -}
+comm : {A B : Set} → A + B → B + A
+comm (Inl x) = Inr x
+comm (Inr x) = Inl x

{- Extensionality for pairs is handled automatically, thanks to record types -}
×-extensional : {A B : Set} (p : A × B) → p ≡ (fst p , snd p)
×-extensional p = refl

-- If we used the non-record definition, we must first pattern match against p
-- This is annoying primarily in situations where we're not in a position to
-- pattern match, such as under an internal λ binding.
data _×'_ (A : Set) (B : Set) : Set where
   _,_ : (fst : A) (snd : B) → A ×' B 

fst' : ∀{A B} → A ×' B → A
fst' (fst , snd) = fst

snd' : ∀{A B} → A ×' B → B
snd' (fst , snd) = snd

×'-extensional : {A B : Set} (p : A ×' B) → p ≡ (fst' p , snd' p)
×'-extensional (fst , snd) = refl
