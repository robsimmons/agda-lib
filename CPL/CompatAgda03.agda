module CompatAgda03 where

    open import Relation.Binary.Core public
      using (_≡_ ; refl)
    open import Data.Nat public 
      renaming (ℕ to Nat ; suc to S ; zero to Z) 
    open import Data.List public 
    open import Data.Product public 
      hiding (map ; zip) renaming (_,_ to _^_ ; ∃ to Σ ; Σ to ∃ ; ,_ to ^_)
    open import Data.Sum public 
      hiding (map) renaming (_⊎_ to Either)
    open import Data.Empty public
      renaming (⊥ to Void ; ⊥-elim to abort)

    Decidable : Set -> Set
    Decidable A = Either A (A → Void)

    sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
    sym refl = refl

    -- List membership. 
    -- As defined by the standard library ∈ is too general and case analysis 
    -- breaks. This restores the definition in Dan's library.
    data _∈_ {A : Set} : A -> List A -> Set where
      i0 : {x : A}   {xs : List A} -> x ∈ (x ∷ xs)
      iS : {x y : A} {xs : List A} -> y ∈ xs -> y ∈ (x ∷ xs)
    infix 10 _∈_

    _⊆_    : {A : Set} -> List A -> List A -> Set
    _⊆_ {A} f f' = ({a : A} -> a ∈ f -> a ∈ f')

    refl⊆ : {A : Set} {l : List A} -> (l ⊆ l)
    refl⊆ inl = inl 
  
    trans⊆ : {A : Set} {l1 l2 l3 : List A} → (l1 ⊆ l2) → (l2 ⊆ l3) → (l1 ⊆ l3)
    trans⊆ s12 s23 in1 = s23 (s12 in1) 

    single⊆ : {A : Set} {l : List A} {b : A} -> (b ∈ l) -> ([ b ] ⊆ l) 
    single⊆ i i0 = i
    single⊆ _ (iS ())

    extend⊆ : ∀ {A x} {l l' : List A} -> l ⊆ l' -> (x ∷ l) ⊆ (x ∷ l')
    extend⊆ w i0 = i0
    extend⊆ w (iS i) = iS (w i)

    i0-app-right : {A : Set} {a : A} (l1 : List A) ( l2 : List A) 
                 -> (a ∈ (l2 ++ (a ∷ l1)))
    i0-app-right l1 [] = i0
    i0-app-right l1 (a ∷ l2) = iS (i0-app-right l1 l2)

    iS-app-right : {A : Set} {a a' : A} (l1 : List A) ( l2 : List A) 
                 -> (a ∈ (l2 ++ l1))
                 -> (a ∈ (l2 ++ (a' ∷ l1)))
    iS-app-right l1 [] i = iS i
    iS-app-right l1 (a ∷ l2) i0 = i0
    iS-app-right l1 (a0 ∷ l2) (iS i) = iS (iS-app-right l1 l2 i)

    append-rh-[] : {A : Set} -> (l : List A) -> (l ++ []) ≡ l
    append-rh-[] [] = refl
    append-rh-[] (h ∷ tl) with (tl ++ []) | append-rh-[] tl 
    ...                       | .tl            | refl = refl

    iswapapp : {A : Set} {a : A} (l1 : List A) ( l2 : List A) -> (a ∈ (l2 ++ l1)) -> (a ∈ (l1 ++ l2))
    iswapapp l1 [] i with l1 ++ [] | append-rh-[] l1
    ...                 | .l1          | refl = i
    iswapapp l1 (a' ∷ l2) i0 = i0-app-right l2 l1
    iswapapp l1 (a' ∷ l2) (iS i) = iS-app-right l2 l1 (iswapapp l1 l2 i)

    splitappend : {A : Set} {a : A} -> (l1 l2 : List A) -> a ∈ (l1 ++ l2) -> Either (a ∈ l1) (a ∈ l2) 
    splitappend [] l2 i = inj₂ i
    splitappend (l ∷ l1) l2 i0 = inj₁ i0 
    splitappend (l ∷ l1) l2 (iS i') with splitappend l1 l2 i' 
    ...                                 | inj₂ inl2 =  inj₂ inl2
    ...                                 | inj₁ inl1 =  inj₁ (iS inl1)

    iSmany : {A : Set} {a : A} (orig : List A) (new : List A) -> (a ∈ orig) -> (a ∈ (new ++ orig))
    iSmany l1 [] i = i
    iSmany l1 (a' ∷ l2) i = iS (iSmany l1 l2 i)

    notin[] : {A C : Set} {x : A} -> x ∈ [] -> C
    notin[] () 

    ⊆refl : {A : Set} {l : List A} -> (l ⊆ l)
    ⊆refl inl = inl 

    ⊆append-cong : {A : Set} {l1 l1' l2 l2' : List A} -> (l1 ⊆ l1') -> (l2 ⊆ l2') -> ((l1 ++ l2) ⊆ (l1' ++ l2'))
    ⊆append-cong {A} {l1} {l1'} {l2} {l2'} s1 s2 inapp 
      with splitappend l1 _ inapp
    ...  | inj₁ in1 = iswapapp l1' l2' (iSmany l1' l2' (s1 in1))
    ...  | inj₂ in2 = iSmany l2' l1' (s2 in2)

    injS : ∀{n m } → (S n) ≡ (S m) → n ≡ m
    injS refl = refl

    respS : ∀{n m } → n ≡ m → (S n) ≡ (S m)
    respS refl = refl

    _≡Nat?_ : (w w' : Nat) → Decidable (w ≡ w')
    Z ≡Nat? Z = inj₁ refl
    Z ≡Nat? (S m) = inj₂ (λ ())
    (S n) ≡Nat? Z = inj₂ (λ ())
    (S n) ≡Nat? (S m) with n ≡Nat? m
    (S n) ≡Nat? (S .n) | inj₁ refl = inj₁ refl
    (S n) ≡Nat? (S m) | inj₂ neq = inj₂ (λ x → neq (injS x))

    notin : ∀{A ws}{w w' : A} 
     → (w ≡ w' → Void) → (w ∈ ws → Void) → (w ∈ (w' ∷ ws) → Void)
    notin f g i0 = f refl
    notin f g (iS iN) = g iN

-- Test

