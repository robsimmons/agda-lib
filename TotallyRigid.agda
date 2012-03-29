module TotallyRigid where

open import Prelude

-- Formulas 
infix 5 _●_
data Form : Set where
   atom : (Q : String) → Form
   _●_ : (A B : Form) → Form
   _->>_ : (A B : Form) → Form
   _>->_ : (A B : Form) → Form

-- Contexts
infix 5 _·_
data SCtx : Set where
   _·_ : (Δ₁ Δ₂ : SCtx) → SCtx
   ⟨_⟩ : (A : Form) → SCtx

dot-elim : ∀{Δ₁ Δ₂ Δ₁' Δ₂'} → (Δ₁ · Δ₂) ≡ (Δ₁' · Δ₂') → (Δ₁ ≡ Δ₁') × (Δ₂ ≡ Δ₂')
dot-elim Refl = Refl , Refl

-- Zipper contexts (standard zippers)
data ZCtx : Set where
   ⟨⟩ : ZCtx
   _·>_ : (Δ : SCtx) (Ω : ZCtx) → ZCtx
   _<·_ : (Ω : ZCtx) (Δ : SCtx) → ZCtx

_⟦_⟧ : ZCtx → SCtx → SCtx
⟨⟩ ⟦ Δ' ⟧ = Δ'
(Δ₁ ·> Ω) ⟦ Δ' ⟧ = Ω ⟦ Δ₁ · Δ' ⟧
(Ω <· Δ₂) ⟦ Δ' ⟧ = Ω ⟦ Δ' · Δ₂ ⟧

_○_ : ZCtx → ZCtx → ZCtx
Ω₁ ○ ⟨⟩ = Ω₁
Ω₁ ○ (Δ ·> Ω) = Δ ·> (Ω₁ ○ Ω)
Ω₁ ○ (Ω <· Δ) = (Ω₁ ○ Ω) <· Δ

-- Holey contexts (inside-out zippers)
-- Having a separate type for them is not strictly necessary, but this is 
-- what types are, in some sense, for in the first place.
data HCtx : Set where
   ⟨⟩ : HCtx
   _·>_ : (Δ : SCtx) (Ω : HCtx) → HCtx
   _<·_ : (Ω : HCtx) (Δ : SCtx) → HCtx

_⟪_⟫ : HCtx → SCtx → SCtx
⟨⟩ ⟪ Δ ⟫ = Δ
(Δ ·> Ω) ⟪ Δ' ⟫ = Δ · Ω ⟪ Δ' ⟫
(Ω <· Δ) ⟪ Δ' ⟫ = Ω ⟪ Δ' ⟫ · Δ

-- Merging holey and zipper contexts
_○⟨_ : ZCtx → HCtx → ZCtx
Ω ○⟨ ⟨⟩ = Ω
Ω ○⟨ (Δ ·> Ω') = (Δ ·> Ω) ○⟨ Ω'
Ω ○⟨ (Ω' <· Δ) = (Ω <· Δ) ○⟨ Ω'

_⟩○_ : ZCtx → HCtx → HCtx
⟨⟩ ⟩○ Ω' = Ω'
(Δ ·> Ω) ⟩○ Ω' = Ω ⟩○ (Δ ·> Ω')
(Ω <· Δ) ⟩○ Ω' = Ω ⟩○ (Ω' <· Δ)

_⟫○_ : (Ω : ZCtx) (Δ : SCtx) → Ω ⟦ Δ ⟧ ≡ (Ω ⟩○ ⟨⟩) ⟪ Δ ⟫ 
Ω ⟫○ Δ = {!!}

⟦⟧⟪⟫ : (Ω₁ Ω₂ : ZCtx) → ∀{Δ₁ Δ₂} → Ω₁ ⟦ Δ₁ ⟧ ≡ Ω₂ ⟦ Δ₂ ⟧ → (Ω₁ ⟩○ ⟨⟩) ⟪ Δ₁ ⟫ ≡ (Ω₂ ⟩○ ⟨⟩) ⟪ Δ₂ ⟫
⟦⟧⟪⟫ Ω₁ Ω₂ eq = {!!}

-- This is basically a "double reversal" theorem
equiv : (Ω : ZCtx) → Ω ≡ ⟨⟩ ○⟨ (Ω ⟩○ ⟨⟩)
equiv Ω = {!!}

-- Sequent calculus for rigid logic. Already suggestive of weak focusing.
infix 4 _⊢_
infix 4 _⟦_⟧⊢_
infix 4 _⊢⟦_⟧
mutual
   data _⊢_ : SCtx → Form → Set where
      L :  ∀{Δ A} {C : Form}
         (Ω : ZCtx)
         (eq : Δ ≡ Ω ⟦ ⟨ A ⟩ ⟧)
         (D : Ω ⟦ A ⟧⊢ C)
         → Δ ⊢ C
      R : ∀{Δ A}
         (D : Δ ⊢⟦ A ⟧)
         → Δ ⊢ A

   data _⊢⟦_⟧ : SCtx → Form → Set where
      _●_ : ∀{Δ₁ Δ₂ A B} 
         → Δ₁ ⊢ A
         → Δ₂ ⊢ B
         → Δ₁ · Δ₂ ⊢⟦ A ● B ⟧
      ΛL : ∀{Δ A B} 
         → ⟨ A ⟩ · Δ ⊢ B
         → Δ ⊢⟦ A >-> B ⟧
      ΛR : ∀{Δ A B} 
         → Δ · ⟨ A ⟩ ⊢ B
         → Δ ⊢⟦ A ->> B ⟧     

   data _⟦_⟧⊢_ : ZCtx → Form → Form → Set where
      let● :  ∀{Ω A B C}
          (D : Ω ⟦ ⟨ A ⟩ · ⟨ B ⟩ ⟧ ⊢ C)
          → Ω ⟦ A ● B ⟧⊢ C
      letL :  ∀{Ω Δ A B C}
          (DA : Δ ⊢ A)
          (D : Ω ⟦ ⟨ B ⟩ ⟧ ⊢ C)
          → (Ω <· Δ) ⟦ A ->> B ⟧⊢ C
      letR : ∀{Ω Δ A B C}
          (DA : Δ ⊢ A)
          (D : Ω ⟦ ⟨ B ⟩ ⟧ ⊢ C)
          → (Δ ·> Ω) ⟦ A >-> B ⟧⊢ C

-- Admissibility of cut
cut : ∀{Ω Δ A C} → Δ ⊢ A → Ω ⟪ ⟨ A ⟩ ⟫ ⊢ C → Ω ⟪ Δ ⟫ ⊢ C
cut {Ω} D E = cut⟪⟫ Ω D E
 where
  mutual
   -- Main theorem, dispatches on left and right rules
   cut⟪⟫ : (Ω : HCtx) → ∀{Δ A C} → Δ ⊢ A → Ω ⟪ ⟨ A ⟩ ⟫ ⊢ C → Ω ⟪ Δ ⟫ ⊢ C
   cut⟪⟫ Ω (R D) (L ΩB eq E) = 
      cutP ⟨⟩ Ω (ΩB ⟩○ ⟨⟩) (equiv ΩB) (eq ≡≡ ΩB ⟫○ ⟨ _ ⟩) D E
   cut⟪⟫ Ω (L ΩB Refl D') E = cutL ΩB Ω D' E
   cut⟪⟫ Ω D (R E') = cutRR Ω refl D E'


   -- Primary cuts
   cutP : ∀{Δ B A C Ω0} 
      (ΩS : ZCtx) (Ω Ω' : HCtx)
      → Ω0 ≡ (ΩS ○⟨ Ω')
      → Ω ⟪ ⟨ A ⟩ ⟫ ≡ Ω' ⟪ ⟨ B ⟩ ⟫
      → Δ ⊢⟦ A ⟧ 
      → Ω0 ⟦ B ⟧⊢ C 
      → (ΩS ⟩○ Ω) ⟪ Δ ⟫ ⊢ C

   -- Principal Cuts
   cutP ΩS ⟨⟩ ⟨⟩ Refl Refl D' E' = {!!}

   -- Right commutative cuts; left rule
   cutP {Δ} {B} {A} ΩS (._ ·> Ω') (Ω0 <· ._) Refl Refl D' E' = {!!}
   cutP {Δ} {B} {A} ΩS (Ω' <· ._) (._ ·> Ω0) Refl Refl D' E' = {!!}

   -- Recursive - keep descending into the backwards zipper closer to the hole
   cutP ΩS (Ω <· Δ) (Ω' <· Δ') Refl eq D' E' with dot-elim eq
   cutP ΩS (Ω <· .Δ) (Ω' <· Δ) Refl eq D' E' | eq1 , Refl = 
      cutP (ΩS <· Δ) Ω Ω' refl eq1 D' E'
   cutP ΩS (Δ' ·> Ω) (Δ0 ·> Ω') Refl eq D' E' with dot-elim eq
   cutP ΩS (.Δ ·> Ω) (Δ ·> Ω') Refl eq D' E' | Refl , eq2 =
      cutP (Δ ·> ΩS) Ω Ω' refl eq2 D' E'

   -- Contradictory cases
   cutP ΩS ⟨⟩ (Δ ·> Ω) Refl () D' E'
   cutP ΩS ⟨⟩ (Ω <· Δ) Refl () D' E'
   cutP ΩS (Δ ·> Ω) ⟨⟩ Refl () D' E'
   cutP ΩS (Ω <· Δ) ⟨⟩ Refl () D' E'

   
   -- Left commutative cuts, left rule applied
   cutL : ∀{A B C}
      (ΩB : ZCtx) (Ω : HCtx) 
      → ΩB ⟦ B ⟧⊢ A
      → Ω ⟪ ⟨ A ⟩ ⟫ ⊢ C
      → Ω ⟪ ΩB ⟦ ⟨ B ⟩ ⟧ ⟫ ⊢ C
   cutL ΩB Ω (let● D') E = {!cut⟪⟫ Ω D' E!}
   cutL (Ω0 <· Δ) Ω (letL DA D') E = {!cut⟪⟫ Ω D' E!}
   cutL (Δ ·> Ω0) Ω (letR DA D') E = {!cut⟪⟫ Ω D' E!}


   -- Right commutative cuts, left rule applied


   -- Right commutative cuts, right rule applied
   cutRR : ∀{Δ Δ' A C}
      (Ω : HCtx)
      → Ω ⟪ ⟨ A ⟩ ⟫ ≡ Δ'
      → Δ ⊢ A
      → Δ' ⊢⟦ C ⟧
      → Ω ⟪ Δ ⟫ ⊢ C
   cutRR ⟨⟩ () D' (E₁ ● E₂)
   cutRR (Δ₁ ·> Ω') Refl D' (E₁ ● E₂) = R (E₁ ● cut⟪⟫ Ω' D' E₂)
   cutRR (Ω' <· Δ') Refl D' (E₁ ● E₂) = R (cut⟪⟫ Ω' D' E₁ ● E₂)
   cutRR Ω Refl D (ΛL E') = R (ΛL (cut⟪⟫ (⟨ _ ⟩ ·> Ω) D E'))
   cutRR Ω Refl D (ΛR E') = R (ΛR (cut⟪⟫ (Ω <· ⟨ _ ⟩) D E'))
  
















compose : (Ω₁ Ω₂ : ZCtx) (Δ : SCtx) → Ω₁ ⟦ Ω₂ ⟦ Δ ⟧ ⟧ ≡ (Ω₁ ○ Ω₂) ⟦ Δ ⟧
compose Ω₁ ⟨⟩ Δ = refl
compose Ω₁ (Δ ·> Ω) Δ' = compose Ω₁ Ω (Δ · Δ')
compose Ω₁ (Ω <· Δ) Δ' = compose Ω₁ Ω (Δ' · Δ)


{-
··elimr : (Δ : SCtx) → {Δ₁ Δ₂ : SCtx} → (Δ ·· Δ₁) ≡ (Δ ·· Δ₂) → Δ₁ ≡ Δ₂
··elimr ∅ eq = eq
··elimr (Δ₁ · Δ₂) {∅} {∅} Refl = refl
··elimr (Δ₁ · Δ₂) {∅} {Δ₁' · Δ₂'} eq = {!eq!}
··elimr (Δ₁ · Δ₂) {∅} {⟨ A ⟩} eq = {!eq!}
··elimr (Δ₁ · Δ₂) {Δ₁' · Δ₂'} {∅} eq = {!eq!}
··elimr (Δ₁ · Δ₂) {.Δ₁0 · .Δ₂0} {Δ₁0 · Δ₂0} Refl = refl
··elimr (Δ₁ · Δ₂) {Δ₁' · Δ₂'} {⟨ A ⟩} ()
··elimr (Δ₁ · Δ₂) {⟨ A ⟩} {∅} eq = {!eq!}
··elimr (Δ₁ · Δ₂) {⟨ A ⟩} {Δ₁' · Δ₂'} ()
··elimr (Δ₁ · Δ₂) {⟨ .A' ⟩} {⟨ A' ⟩} Refl = refl
··elimr ⟨ A ⟩ {∅} {∅} eq = refl
··elimr ⟨ A ⟩ {Δ₁ · Δ₂} {∅} ()
··elimr ⟨ A ⟩ {⟨ A' ⟩} {∅} ()
··elimr ⟨ A ⟩ {∅} {Δ₁' · Δ₂} ()
··elimr ⟨ A ⟩ {.Δ₁' · .Δ₂'} {Δ₁' · Δ₂'} Refl = refl
··elimr ⟨ A ⟩ {⟨ A' ⟩} {Δ₁' · Δ₂} ()
··elimr ⟨ A ⟩ {∅} {⟨ A' ⟩} ()
··elimr ⟨ A ⟩ {Δ₁ · Δ₂} {⟨ A' ⟩} ()
··elimr ⟨ A ⟩ {⟨ .A0 ⟩} {⟨ A0 ⟩} Refl = refl


⟦⟧elim (Δ ·> Ω) eq = {!··elimr Δ!}
⟦⟧elim (Ω <· Δ) eq = {!!}
-}
⟦⟧elim : (Ω : ZCtx) {Δ₁ Δ₂ : SCtx} → Ω ⟦ Δ₁ ⟧ ≡ Ω ⟦ Δ₂ ⟧ → Δ₁ ≡ Δ₂
⟦⟧elim ⟨⟩ eq = eq
⟦⟧elim (Δ ·> Ω) {Δ₁}{Δ₂} eq with ⟦⟧elim Ω {Δ · Δ₁} {Δ · Δ₂} eq
⟦⟧elim (Δ ·> Ω) eq | Refl = refl
⟦⟧elim (Ω <· Δ) {Δ₁}{Δ₂} eq with ⟦⟧elim Ω {Δ₁ · Δ} {Δ₂ · Δ} eq
⟦⟧elim (Ω <· Δ) eq | Refl = refl


{-
inside·> : (Δ' : ZCtx) (Δ₂ : SCtx)
   → ∃ λ Ω' → (Δ₁ : SCtx) → Ω' ⟦ Δ₁ ⟧ ≡ Δ' ⟦ Δ₁ ·· Δ₂ ⟧
inside·> ⟨⟩ Δ₂' = ⟨⟩ <· Δ₂' , λ Δ₁ → ?
inside·> (Δ₁ ·> Δ₂) Δ₂' with inside·> Δ₂ Δ₂' 
... | Ω' , eq = Δ₁ ·> Ω' , λ Δ₁' → resp (λ Δ → Δ₁ ·· Δ) (eq Δ₁')
inside·> (Δ₁ <· Δ₂) Δ₂' with inside·> Δ₁ Δ₂' 
... | Ω' , eq = Ω' <· Δ₂ , λ Δ₁' → resp (λ Δ → Δ ·· Δ₂) (eq Δ₁')

inside<· : (Δ' : ZCtx) (Δ₁ : SCtx)
   → ∃ λ Ω' → (Δ₂ : SCtx) → Ω' ⟦ Δ₂ ⟧ ≡ Δ' ⟦ Δ₁ ·· Δ₂ ⟧
inside<· ⟨⟩ Δ₁' = Δ₁' ·> ⟨⟩ , λ Δ₁ → refl
inside<· (Δ₁ ·> Δ₂) Δ₂' with inside<· Δ₂ Δ₂' 
... | Ω' , eq = Δ₁ ·> Ω' , λ Δ₁' → resp (λ Δ → Δ₁ ·· Δ) (eq Δ₁')
inside<· (Δ₁ <· Δ₂) Δ₂' with inside<· Δ₁ Δ₂' 
... | Ω' , eq = Ω' <· Δ₂ , λ Δ₁' → resp (λ Δ → Δ ·· Δ₂) (eq Δ₁')
-}


{-
   cutP : ∀{Δ B A C} 
      (ΩS Ω Ω' : ZCtx)
      → Ω ⟦ ⟨ A ⟩ ⟧ ≡ Ω' ⟦ ⟨ B ⟩ ⟧
      → Δ ⊢⟦ A ⟧ 
      → ΩS ○ Ω' ⟦ B ⟧⊢ C 
      → ΩS ⟦ Ω ⟦ Δ ⟧ ⟧ ⊢ C
   cutP ΩS ⟨⟩ ⟨⟩ Refl (D₁ ● D₂) (let● E') =  
      cut' (ΩS <· _) D₁ (cut' (⟨ _ ⟩ ·> ΩS) D₂ E')
   cutP .(Δ' ·> Ω) ⟨⟩ ⟨⟩ Refl (ΛL y) (letR {Ω} {Δ'} DA D') = 
      cut' Ω (cut' (⟨⟩ <· _) DA y) D'
   cutP .(Ω <· Δ') ⟨⟩ ⟨⟩ Refl (ΛR y) (letL {Ω} {Δ'} DA D') = 
      cut' Ω (cut' (_ ·> ⟨⟩) DA y) D'
   cutP ΩS ⟨⟩ (Δ' ·> Ω) eq D' E' = {!CONTRADICTION!}
   cutP ΩS ⟨⟩ (Ω <· Δ') eq D' E' = {!CONTRADICTION!}
   cutP ΩS (Δ' ·> Ω) ⟨⟩ eq D' E' = {!CONTRADICTION!}
   cutP ΩS (Δ' ·> Ω) (Δ0 ·> Ω') eq D' E' = {!!}
   cutP ΩS (Δ' ·> Ω) (Ω' <· Δ0) eq D' E' = {!!}
   cutP ΩS (Ω <· Δ') ⟨⟩ eq D' E' = {!CONTRADICTION!}
   cutP ΩS (Ω <· Δ') (Δ0 ·> Ω') eq D' E' = {!!}
   cutP ΩS (Ω <· Δ') (Ω' <· Δ0) eq D' E' = {!!}
-}
{- with eq
   cutP ΩS ⟨⟩ ⟨⟩ eq One (let1 D') | Refl = D'
   cutP {Ω₁ · Ω₂} ΩS ⟨⟩ ⟨⟩ eq (D₁ ● D₂) (let● E') | Refl = 
      coe {! YES!} 
      (cut' (ΩS <· Ω₂) D₁ (cut' (⟨ _ ⟩ ·> ΩS) D₂ E'))
   cutP {Δ} .(Ω' <· Δ') ⟨⟩ ⟨⟩ eq (ΛL D') (letR {Ω'}{Δ'} EA E') | Refl = {!cut' (⟨⟩ <· Δ) EA!}
   cutP {Δ} .(_ ·> _) ⟨⟩ ⟨⟩ eq (ΛR D') (letL  EA E') | Refl = {!!}
   cutP ΩS ⟨⟩ (Δ' ·> Ω) eq D' E' = {! !}
   cutP ΩS ⟨⟩ (Ω <· Δ') eq D' E' = {!!}
   cutP ΩS (Δ' ·> Ω) Ω' eq D' E' = {!!}
   cutP ΩS (Ω <· Δ') Ω' eq D' E' = {!!} -}

{-
   cutL : (Ω ΩB : ZCtx) 
      → ∀{Δ B A C} 
      → Δ ≡ ΩB ⟦ ⟨ B ⟩ ⟧
      → ΩB ⟦ B ⟧⊢ A 
      → Ω ⟦ ⟨ A ⟩ ⟧ ⊢ C 
      → Ω ⟦ ΩB ⟦ ⟨ B ⟩ ⟧ ⟧ ⊢ C
   cutL Ω ΩB {C = C} eq (let1 D') E' =
      L (Ω ○ ΩB) (compose Ω ΩB _)
      (let1 (coe (resp (λ x → x ⊢ C) (compose Ω ΩB _)) (cut' Ω D' E')))
   cutL Ω ΩB eq (let● D') E' = {!!}
   cutL Ω (Ω' <· Δ') eq (letR DA D') E' = {!!}
   cutL Ω (Δ' ·> Ω') eq (letL DA D') E' = {!!}
-}

 --  {!L (Ω ○ ΩB) (compose Ω ΩB (⟨ One ⟩)) ?!}

{-   cut' {Ω} 1R E = rcomm Ω 1R refl E 1L
   cut' {Ω} (●R D₁ D₂) E = rcomm Ω (●R D₁ D₂) {!!} E {!!}
   cut' (->>R D) E = {!!}
   cut' (>->R D) E = {!!}

   rcomm : (Ω' : ZCtx) → ∀{Ω Δ A C} 
      → Δ ⊢ A
      → Ω ≡ Ω' ⟦ ⟨ A ⟩ ⟧
      → Ω ⊢ C 
      → (∀{Ω''} → Ω'' ⟦ Δ ⟧ ⊢ C → Ω'' ⟦ A ⟧⊢ C) 
      → Ω' ⟦ Δ ⟧ ⊢ C
   rcomm D E f = {!E!}
-}

{-
   prin● : (A B C : Form) (Δ' : ZCtx) (Δ₁ Δ₂ : SCtx) 
      → Δ₁ ⊢ A 
      → Δ₂ ⊢ B 
      → Δ ≡ Δ' ⟦ ⟨ A ⟩ · ⟨ B ⟩ ⟧ 
      → Δ' ⟦ ⟨ A ⟩ · Δ₂ ⟧ ⊢ C 
      → Δ' ⟦ ⟨ A ⟩ · ⟨ B ⟩ ⟧ ⊢ C
   prin● A B C Δ' Δ₁ Δ₂ D₁ D₂ E with inside·> Δ' (⟨ B ⟩) | inside<· Δ' (Δ₁)
   ... | ΩB , eqB | ΩA , eqA = {!cut' {ΩA} D₂ (coe (resp (λ x → x ⊢ C)  (symm (eqA Δ₂ ≡≡ lem Δ' Δ₁ Δ₂ E))) E) !}
-}

{-
   ... | y with cut' {Ω>} D₁ (coe (symm (resp (λ x' → x' ⊢ C) (eq> ⟨ A ⟩))) {!eq!})
   ... | x = {!!}
-}

{-
with cut' {Ω'} D₁ (coe (resp (λ x → x ⊢ C) (symm (eq _ ≡≡ {!lem Δ' _ Δ₂ E!}))) E)
   ... | x = {!!}
-}

