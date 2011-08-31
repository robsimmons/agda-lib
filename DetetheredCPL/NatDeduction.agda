-- Constructive Provability Logic 
-- De-tethered intuitionstic variant
-- Robert J. Simmons, Bernardo Toninho

-- Natural deduction and substitution

module DetetheredCPL.NatDeduction where
open import Prelude hiding (⊥)
open import Accessibility.Inductive
open import Accessibility.IndexedList
open import DetetheredCPL.Core

module NAT-DEDUCTION (UWF : UpwardsWellFounded) where 
   open TRANS-UWF UWF
   open ILIST UWF
   open CORE UWF



   -- Weakening Principle
   module WK-N where 
      wkP : W → Set 
      wkP = λ w → ∀{Γ Γ' A} → Γ ⊆ Γ' to w → Γ ⊢ A [ w ] → Γ' ⊢ A [ w ]

      wk' : (w : W) → ((w' : W) → w ≺+ w' → wkP w') → wkP w
      wk' w ih = wk
       where
        mutual
         wk≺* : ∀{Γ Γ' v A} → w ≺* v → Γ ⊆ Γ' to w → Γ ⊢ A [ v ] → Γ' ⊢ A [ v ]
         wk≺* ≺*≡ sub D = wk sub D
         wk≺* (≺*+ ω) sub D = ih _ ω (⊆to/≺+ ω sub) D 

         wk≺ : ∀{Γ Γ' v A} → w ≺ v → Γ ⊆ Γ' to w → Γ ⊢ A [ v ] → Γ' ⊢ A [ v ]
         wk≺ ω sub D = ih _ (≺+0 ω) (⊆to/≺+ (≺+0 ω) sub) D

         wk≺+ : ∀{Γ Γ' v A} → w ≺+ v → Γ ⊆ Γ' to w → Γ' ⊢ A [ v ] → Γ ⊢ A [ v ]
         wk≺+ ω sub D = ih _ ω (⊆to/≺+' ω sub) D

         wk : ∀{Γ Γ' A} → Γ ⊆ Γ' to w → Γ ⊢ A [ w ] → Γ' ⊢ A [ w ]
         wk sub (hyp x) = hyp (⊆to/now sub x)
         wk sub (⊃I D₁) = ⊃I (wk (⊆to/both sub) D₁)
         wk sub (⊃E D₁ D₂) = ⊃E (wk sub D₁) (wk sub D₂)
         wk sub (⊥E ωh D₁) = ⊥E ωh (wk≺* ωh sub D₁)
         wk sub (◇I ω D₁) = ◇I ω (wk≺ ω sub D₁)
         wk sub (◇E ωh D₁ D₂) = ◇E ωh (wk≺* ωh sub D₁) 
            λ ω D₀ → wk sub (D₂ ω (wk≺+ (≺*S' ωh ω) sub D₀))
         wk sub (□I D₁) = □I (λ ω → wk≺ ω sub (D₁ ω))
         wk sub (□E ωh D₁ D₂) = □E ωh (wk≺* ωh sub D₁) 
            λ D₀ → wk sub (D₂ λ ω → wk≺+ (≺*S' ωh ω) sub (D₀ ω))

      wkN : ∀{Γ Γ' A w} → Γ ⊆ Γ' to w → Γ ⊢ A [ w ] → Γ' ⊢ A [ w ]
      wkN sub D = ind+ wkP wk' _ sub D
 
   open WK-N public using (wkN)



   -- Simultaneous substitutions
   data _⊆_pr_ (Δ Γ : MCtx) (w : W) : Set where
      st : (∀{A w'} (ω : w ≺* w') (x : A at w' ∈ Δ) → Γ ⊢ A [ w' ])
         → (∀{A w'} (ω : w ≺+ w') (x : A at w' ∈ Γ) → Δ ⊢ A [ w' ])
         → Δ ⊆ Γ pr w

   -- Elimination forms
   ⊆pr : ∀{Γ Δ A w} → Δ ⊆ Γ pr w → A at w ∈ Δ → Γ ⊢ A [ w ]
   ⊆pr (st sub _) x = sub ≺*≡ x

   ⊆pr* : ∀{Γ Δ A w w'} 
      → w ≺* w' 
      → Δ ⊆ Γ pr w 
      → A at w' ∈ Δ 
      → Γ ⊢ A [ w' ]
   ⊆pr* ω (st sub _) x = sub ω x

   ⊆pr+ : ∀{Γ Δ A w w'} 
      → w ≺+ w' 
      → Δ ⊆ Γ pr w 
      → A at w' ∈ Δ 
      → Γ ⊢ A [ w' ]
   ⊆pr+ ω (st sub _) x = sub (≺*+ ω) x

   ⊆pr+' : ∀{Γ Δ A w w'} 
      → w ≺+ w' 
      → Δ ⊆ Γ pr w 
      → A at w' ∈ Γ 
      → Δ ⊢ A [ w' ]
   ⊆pr+' ω (st _ sub) x = sub ω x

   -- Introduction/manipulation forms
   ⊆pr/refl : ∀{Γ w} → Γ ⊆ Γ pr w
   ⊆pr/refl = st (λ ω x → hyp x) (λ ω x → hyp x)

   ⊆pr/wken : ∀{Γ Δ A w} → Δ ⊆ Γ pr w → Δ ⊆ (A at w :: Γ) pr w
   ⊆pr/wken {Γ} {Δ} {B} {w} (st sub sub≺) = 
      st (λ ω → wkN (⊆to/wken* ω (⊆to/refl _)) o sub ω) sub≺'
    where
      sub≺' : ∀{A w'} → w ≺+ w' 
         → A at w' ∈ (B at w :: Γ) 
         → Δ ⊢ A [ w' ]
      sub≺' ω Z = abort (≺+⊀ ω ≺*≡)
      sub≺' ω (S x) = sub≺ ω x

   ⊆pr/xtndL' : ∀{Γ A w w'} → Γ ⊢ A [ w' ] → (A at w' :: Γ) ⊆ Γ pr w
   ⊆pr/xtndL' {Γ} {B} {w} {w''} D = 
      st (λ _ → sub') (λ _ → hyp o S)
    where
      sub' : ∀{A w'} 
         → A at w' ∈ (B at w'' :: Γ) 
         → Γ ⊢ A [ w' ]
      sub' Z = D
      sub' (S x) = hyp x

   ⊆pr/xtndR' : ∀{Γ A w w'} → Γ ⊢ A [ w' ] → Γ ⊆ (A at w' :: Γ) pr w
   ⊆pr/xtndR' {Γ} {B} {w} {w''} D = 
      st (λ _ → hyp o S) (λ _ → sub≺')
    where
      sub≺' : ∀{A w'} 
         → A at w' ∈ (B at w'' :: Γ) 
         → Γ ⊢ A [ w' ]
      sub≺' Z = D
      sub≺' (S x) = hyp x

   ⊆pr/both : ∀{Γ Δ A w} → Δ ⊆ Γ pr w → (A at w :: Δ) ⊆ (A at w :: Γ) pr w
   ⊆pr/both {Γ} {Δ} {B} {w} (st sub sub≺) = st sub' sub≺'
    where
      sub' : ∀{A w'} → w ≺* w'
         → A at w' ∈ (B at w :: Δ) 
         → (B at w :: Γ) ⊢ A [ w' ] 
      sub' ω Z = hyp Z
      sub' ω (S x) = wkN (⊆to/wken* ω (⊆to/refl _)) (sub ω x)
   
      sub≺' : ∀{A w'} → w ≺+ w'
         → A at w' ∈ (B at w :: Γ) 
         → (B at w :: Δ) ⊢ A [ w' ] 
      sub≺' ω Z = abort (≺+⊀ ω ≺*≡)
      sub≺' ω (S x) = wkN (⊆to/wkenirrev (≺+⊀ ω) (⊆to/refl _)) (sub≺ ω x) 

   ⊆pr/≺ : ∀{Γ Δ w w'} → w ≺ w' → Δ ⊆ Γ pr w → Δ ⊆ Γ pr w'
   ⊆pr/≺ ω (st sub sub≺) = st 
      (λ ω' → sub (≺*+ (≺*S ω ω')))
      (λ ω' → sub≺ (≺+S ω ω'))

   ⊆pr/≺* : ∀{Γ Δ w w'} → w ≺* w' → Δ ⊆ Γ pr w → Δ ⊆ Γ pr w'
   ⊆pr/≺* ω (st sub sub≺) = st 
      (λ ω' → sub (≺*trans ω ω')) 
      (λ ω' → sub≺ (≺*+trans ω ω'))

   ⊆pr/≺+ : ∀{Γ Δ w w'} → w ≺+ w' → Δ ⊆ Γ pr w → Δ ⊆ Γ pr w'
   ⊆pr/≺+ ω (st sub sub≺) = st 
      (λ ω' → sub (≺*+ (≺+*trans ω ω'))) 
      (λ ω' → sub≺ (≺+trans ω ω'))

   ⊆pr/≺+' : ∀{Γ Δ w w'} → w ≺+ w' → Δ ⊆ Γ pr w → Γ ⊆ Δ pr w'
   ⊆pr/≺+' ω (st sub sub≺) = st 
      (λ ω' → sub≺ (≺+*trans ω ω'))
      (λ ω' → sub (≺*+ (≺+trans ω ω')))



   -- Substitution principle
   module SUBST where
      substP : W → Set 
      substP = λ w → ∀{A Δ Γ} → Δ ⊆ Γ pr w → Δ ⊢ A [ w ] → Γ ⊢ A [ w ]

      subst' : (w : W) → ((w' : W) → w ≺+ w' → substP w') → substP w
      subst' w ih = subst 
       where
        mutual
         subst≺* : ∀{A Δ Γ v} → w ≺* v → Δ ⊆ Γ pr w → Δ ⊢ A [ v ] → Γ ⊢ A [ v ]
         subst≺* ≺*≡ sub D = subst sub D
         subst≺* (≺*+ ω) sub D = ih _ ω (⊆pr/≺+ ω sub) D

         subst≺ : ∀{A Δ Γ v} → w ≺ v → Δ ⊆ Γ pr w → Δ ⊢ A [ v ] → Γ ⊢ A [ v ]
         subst≺ ω sub D = ih _ (≺+0 ω) (⊆pr/≺ ω sub) D

         subst≺+ : ∀{A Δ Γ v} → w ≺+ v → Δ ⊆ Γ pr w → Γ ⊢ A [ v ] → Δ ⊢ A [ v ]
         subst≺+ ω sub D = ih _ ω (⊆pr/≺+' ω sub) D

         subst : ∀{A Δ Γ} → Δ ⊆ Γ pr w → Δ ⊢ A [ w ] → Γ ⊢ A [ w ]
         subst sub (hyp x) = ⊆pr sub x
         subst sub (⊃I D₁) = ⊃I (subst (⊆pr/both sub) D₁)
         subst sub (⊃E D₁ D₂) = ⊃E (subst sub D₁) (subst sub D₂)
         subst sub (⊥E ωh D₁) = ⊥E ωh (subst≺* ωh sub D₁)
         subst sub (◇I ω D₁) = ◇I ω (subst≺ ω sub D₁)
         subst sub (◇E ωh D₁ D₂) = ◇E ωh (subst≺* ωh sub D₁) 
            λ ω D₀ → subst sub (D₂ ω (subst≺+ (≺*S' ωh ω) sub D₀))
         subst sub (□I D₁) = □I (λ ω → subst≺ ω sub (D₁ ω))
         subst sub (□E ωh D₁ D₂) = □E ωh (subst≺* ωh sub D₁) 
            λ D₀ → subst sub (D₂ λ ω → subst≺+ (≺*S' ωh ω) sub (D₀ ω))

      ssubst : ∀{A Δ Γ w} → Δ ⊆ Γ pr w → Δ ⊢ A [ w ] → Γ ⊢ A [ w ]
      ssubst sub D = ind+ substP subst' _ sub D

      subst : ∀{A Γ w w' C} 
         → w ≺* w' 
         → Γ ⊢ A [ w' ] 
         → (A at w' :: Γ) ⊢ C [ w ] 
         → Γ ⊢ C [ w ]
      subst {B} {Γ} {w} {w''} {C}  ω D E = ssubst (⊆pr/xtndL' D) E
       where
         sub' : ∀{A w'} → w ≺* w' → A at w' ∈ B at w'' :: Γ → Γ ⊢ A [ w' ] 
         sub' ω' Z = D
         sub' ω' (S x) = hyp x

      ⊆pr/trans : ∀{Δ₁ Δ₂ Δ₃ w} → Δ₁ ⊆ Δ₂ pr w → Δ₂ ⊆ Δ₃ pr w → Δ₁ ⊆ Δ₃ pr w
      ⊆pr/trans sub1 sub2 = st 
         (λ ω x → ssubst (⊆pr/≺* ω sub2) (⊆pr* ω sub1 x)) 
         (λ ω x → ssubst (⊆pr/≺+' ω sub1) (⊆pr+' ω sub2 x)) 

   open SUBST public using (ssubst ; subst ; ⊆pr/trans)


   ⊆pr/xtndL : ∀{Γ Δ A w w'}
      → Δ ⊆ Γ pr w
      → Δ ⊢ A [ w' ] 
      → (A at w' :: Δ) ⊆ Γ pr w
   ⊆pr/xtndL sub D = ⊆pr/trans (⊆pr/xtndL' D) sub

   ⊆pr/xtndR : ∀{Γ Δ A w w'} 
      → Δ ⊆ Γ pr w 
      → Γ ⊢ A [ w' ] 
      → Δ ⊆ (A at w' :: Γ) pr w
   ⊆pr/xtndR sub D = ⊆pr/trans sub (⊆pr/xtndR' D)

{-

   -- Manipulating the substitution principle

   ⊆pr/xtnd' : ∀{Δ Γ A w w'} → Γ ⊢ A [ w' ] → Δ ⊆ Γ pr w → (A at w' :: Δ) ⊆ Γ pr w
   ⊆pr/xtnd' {Δ} {Γ} {B} {w} {w''} D (st sub sub≺) = 
      st sub' (λ ω x → ssubst {!⊆pr/xtnd!} (sub≺ ω x))
    where
      sub' : ∀{A w'} 
         → w ≺* w'
         → A at w' ∈ (B at w'' :: Δ) 
         → Γ ⊢ A [ w' ]
      sub' ω Z = D
      sub' ω (S x) = sub ω x


   ⊆pr/wken≺+ : ∀{Γ Δ A w w'} 
      → w ≺+ w' 
      → Δ ⊢ A [ w' ]
      → Δ ⊆ Γ pr w 
      → Δ ⊆ (A at w' :: Γ) pr w
   ⊆pr/wken≺+ {Γ} {Δ} {B} {w} {w''} ωh D (st sub sub≺) = 
      st {!!} {! sub≺' !} 
    where
      sub' : ∀{A w'} → w ≺* w'
         → A at w' ∈ Δ
         → B at w'' :: Γ ⊢ A [ w' ] 
      sub' ω x = {! sub ω x !}
 
      sub≺' : ∀{A w'} → w ≺+ w' 
         → A at w' ∈ Γ 
         → (B at w'' :: Δ) ⊢ A [ w' ]
      sub≺' {w' = w'} ω x with dec≺ w' w''
      sub≺' ω x | Inl ≺*≡ = wkN wken (sub≺ ω x)
      sub≺' ω x | Inl (≺*+ ω') = ssubst {!!} (sub≺ ω x)
      sub≺' ω x | Inr ω' = {!!}


   ⊆pr/wken≺* : ∀{Γ Δ A w w'} 
      → w ≺* w' 
      → Δ ⊢ A [ w' ]
      → Δ ⊆ Γ pr w 
      → (A at w' :: Δ) ⊆ Γ pr w
   ⊆pr/wken≺* {Γ} {Δ} {B} {w} {w''} ωh D (st sub sub≺) = 
      st sub' {! sub≺' !} 
    where
      sub' : ∀{A w'} → w ≺* w'
         → A at w' ∈ B at w'' :: Δ
         → Γ ⊢ A [ w' ] 
      sub' ω Z = ssubst (⊆pr/≺* ωh (st sub sub≺)) D 
      sub' ω (S x) = sub ω x
 
      sub≺' : ∀{A w'} → w ≺+ w' 
         → A at w' ∈ Γ 
         → (B at w'' :: Δ) ⊢ A [ w' ]
      sub≺' {w' = w'} ω x with dec≺ w' w''
      sub≺' ω x | Inl ≺*≡ = wkN wken (sub≺ ω x)
      sub≺' ω x | Inl (≺*+ ω') = ssubst {!!} (sub≺ ω x)
      sub≺' ω x | Inr ω' = {!!}
-}