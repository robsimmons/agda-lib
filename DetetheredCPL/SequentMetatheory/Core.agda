-- Constructive Provability Logic 
-- De-tethered intuitionistic variant
-- Robert J. Simmons, Bernardo Toninho

module DetetheredCPL.SequentMetatheory.Core where
open import Prelude hiding (⊥)
open import Accessibility.Inductive 
open import Accessibility.IndexedList
open import DetetheredCPL.Core 

module SEQUENT-CORE 
  (UWF : UpwardsWellFounded 
   ; dec≺ : (w w' : _) → Decidable (TRANS-UWF._≺*_ UWF w w')) where
   open TRANS-UWF UWF
   open ILIST UWF
   open CORE UWF 



   -- Structural metric
   data Shape : Set where
      Z : Shape
      S : Shape → Shape
      _,_ : Shape → Shape → Shape
      ◇L : ∀{w A Δ} → (∀{w'} → w ≺ w' → Δ ⇒ A [ w' ] → Shape) → Shape
      □L : ∀{w A Δ} → ((∀{w'} → w ≺ w' → Δ ⇒ A [ w' ]) → Shape) → Shape

   infix 4 _/_⇒_[_]/_
   data _/_⇒_[_]/_ (Δ Γ : MCtx) : Type → (w : W) → Shape → Set where
      hyp : ∀{w Q} 
         → (x : a Q at w ∈ Γ)
         → Δ / Γ ⇒ a Q [ w ]/ Z
      ⊃R : ∀{w A B s} 
         → (D₁ : Δ / A at w :: Γ ⇒ B [ w ]/ s)
         → Δ / Γ ⇒ (A ⊃ B) [ w ]/ S s
      ⊃L : ∀{A B wc C s₁ s₂}
         → (x : (A ⊃ B) at wc ∈ Γ)
         → (D₁ : Δ / Γ ⇒ A [ wc ]/ s₁)
         → (D₂ : Δ / B at wc :: Γ ⇒ C [ wc ]/ s₂)
         → Δ / Γ ⇒ C [ wc ]/ s₁ , s₂
      ⊃L+ : ∀{A B w wc C s}
         → (ωh : wc ≺+ w)
         → (x : (A ⊃ B) at w ∈ Γ)
         → (D₁ : Δ ⇒ A [ w ])
         → (D₂ : Δ / B at w :: Γ ⇒ C [ wc ]/ s)
         → Δ / Γ ⇒ C [ wc ]/ S s
      ⊥L : ∀{w wc C} 
         → (ωh : wc ≺* w)
         → (x : ⊥ at w ∈ Γ)
         → Δ / Γ ⇒ C [ wc ]/ Z
      ◇R : ∀{w' w A}
         → (ω : w ≺ w')
         → (D₁ : Δ ⇒ A [ w' ])
         → Δ / Γ ⇒ ◇ A [ w ]/ Z
      ◇L : ∀{wc w C A} 
         → {s : ∀{w'} → w ≺ w' → Δ ⇒ A [ w' ] → Shape}
         → (ωh : wc ≺* w)
         → (x : (◇ A) at w ∈ Γ)
         → (D₁ : ∀{w'} 
            → (ω : w ≺ w') 
            → (D₀ : Δ ⇒ A [ w' ])
            → Δ / Γ ⇒ C [ wc ]/ s ω D₀)
         → Δ / Γ ⇒ C [ wc ]/ ◇L s
      □R : ∀{A w}
         → (D₁ : ∀{w'} (ω : w ≺ w') → Δ ⇒ A [ w' ]) 
         → Δ / Γ ⇒ □ A [ w ]/ Z
      □L : ∀{A C w wc}
         → {s : (∀{w'} → w ≺ w' → Δ ⇒ A [ w' ]) → Shape} 
         → (ωh : wc ≺* w)
         → (x : (□ A) at w ∈ Γ)
         → (D₁ : (D₀ : ∀{w'} (ω : w ≺ w') → Δ ⇒ A [ w' ]) 
            → Δ / Γ ⇒ C [ wc ]/ s D₀)
         → Δ / Γ ⇒ C [ wc ]/ □L s


   -- Identity Principle (Unfortunately, currently used in cut/decut)
   identity' : ∀{Γ w} (A : Type) → A at w ∈ Γ → Γ ⇒ A [ w ]
   identity' (a N) x = hyp x
   identity' ⊥ x = ⊥L ≺*≡ x
   identity' (A ⊃ B) x = ⊃R (⊃L ≺*≡ (S x) (identity' A Z) (identity' B Z))
   identity' (◇ A) x = ◇L ≺*≡ x (λ ω D₀ → ◇R ω D₀)
   identity' (□ A) x = □L ≺*≡ x (λ D₀ → □R D₀)

   identity : ∀{Γ w} (A : Type) → A at w :: Γ ⇒ A [ w ]
   identity A = identity' A Z




   -- Weakening (outside the metric)
   wk : ∀{Γ Γ' w A}
      → Γ ⊆ Γ' to w
      → Γ ⇒ A [ w ] 
      → Γ' ⇒ A [ w ]
   wk = ind+ wkP wk' _ ≺*≡
    where
      wkP : W → Set
      wkP = λ w → ∀{Γ Γ' A w'} 
         → w ≺* w'
         → Γ ⊆ Γ' to w  
         → Γ ⇒ A [ w' ] 
         → Γ' ⇒ A [ w' ]

      wk' : (w : W) → ((w' : W) → w ≺+ w' → wkP w') → wkP w
      wk' w ih ω* sub (hyp x) = hyp (⊆to* ω* sub x)
      wk' w ih ω* sub (⊃R D) = ⊃R (wk' w ih ω* (⊆to/both sub) D) 
      wk' w ih ω* sub (⊃L ωh x D D') = 
         ⊃L ωh (⊆to* (≺*trans ω* ωh) sub x) (wk' w ih (≺*trans ω* ωh) sub D) 
          (wk' w ih ω* (⊆to/both sub) D')
      wk' w ih ω* sub (⊥L ωh x) = ⊥L ωh (⊆to* (≺*trans ω* ωh) sub x) 
      wk' w ih ω* sub (◇R ω D) = ◇R ω (wk' w ih (≺*+ (≺*S' ω* ω)) sub D) 
      wk' w ih ω* sub (◇L ωh x D) = ◇L ωh (⊆to* ω' sub x) 
         λ ω D₀ → wk' w ih ω* sub 
          (D ω (ih _ (≺*S' ω' ω) ≺*≡ (⊆to/≺+' (≺*S' ω' ω) sub) D₀))
       where
         ω' = (≺*trans ω* ωh)
      wk' w ih ω* sub (□R D₁) = 
         □R λ ω → wk' w ih (≺*+ (≺*S' ω* ω)) sub (D₁ ω)
      wk' w ih ω* sub (□L ωh x D₁) = □L ωh (⊆to* (≺*trans ω* ωh) sub x) 
         λ D₀ → wk' w ih ω* sub (D₁ 
          λ ω → ih _ (≺*+trans ω* (≺*S' ωh ω)) ≺*≡ 
           (⊆to/≺+' (≺*+trans ω* (≺*S' ωh ω)) sub) (D₀ ω))



   -- Weakening in the metric
   wkM : ∀{Δ Γ Γ' w A s}
      → Γ ⊆ Γ' to w
      → Δ / Γ ⇒ A [ w ]/ s
      → Δ / Γ' ⇒ A [ w ]/ s
   wkM sub (hyp x) = hyp (⊆to/now sub x)
   wkM sub (⊃R D₁) = ⊃R (wkM (⊆to/both sub) D₁) 
   wkM sub (⊃L x D₁ D₂) = 
      ⊃L (⊆to/now sub x) (wkM sub D₁) (wkM (⊆to/both sub) D₂)
   wkM sub (⊃L+ ωh x D₁ D₂) = 
      ⊃L+ ωh (⊆to/later ωh sub x) D₁ (wkM (⊆to/both sub) D₂)
   wkM sub (⊥L ωh x) = ⊥L ωh (⊆to* ωh sub x)
   wkM sub (◇R ω' D₁) = ◇R ω' D₁
   wkM sub (◇L ωh x  D₁) = ◇L ωh (⊆to* ωh sub x) 
      λ ω D₀ → wkM sub (D₁ ω D₀)
   wkM sub (□R D₁) = □R D₁
   wkM sub (□L ωh x D₁) = □L ωh (⊆to* ωh sub x) 
      λ D₀ → wkM sub (D₁ D₀)



   -- Judgmental principle, based on provability
   data _⊆_pr_ (Δ Γ : MCtx) (w : W) : Set where
      st : (∀{A w'} → w ≺* w' → A at w' ∈ Δ → Γ ⇒ A [ w' ])
         → (∀{A w'} → w ≺+ w' → A at w' ∈ Γ → Δ ⇒ A [ w' ])
         → Δ ⊆ Γ pr w

   -- Elimination forms
   ⊆pr/now : ∀{Γ Δ A w} → Δ ⊆ Γ pr w → A at w ∈ Δ → Γ ⇒ A [ w ]
   ⊆pr/now (st sub _) x = sub ≺*≡ x

   ⊆pr/soon : ∀{Γ Δ A w w'} 
      → w ≺* w' 
      → Δ ⊆ Γ pr w 
      → A at w' ∈ Δ 
      → Γ ⇒ A [ w' ]
   ⊆pr/soon ω (st sub _) x = sub ω x

   ⊆pr/later : ∀{Γ Δ A w w'} 
      → w ≺+ w' 
      → Δ ⊆ Γ pr w 
      → A at w' ∈ Δ 
      → Γ ⇒ A [ w' ]
   ⊆pr/later ω (st sub _) x = sub (≺*+ ω) x

   ⊆pr/later' : ∀{Γ Δ A w w'} 
      → w ≺+ w' 
      → Δ ⊆ Γ pr w 
      → A at w' ∈ Γ 
      → Δ ⇒ A [ w' ]
   ⊆pr/later' ω (st _ sub) x = sub ω x

   -- Introduction forms
   ⊆pr/refl : ∀{Γ w} → Γ ⊆ Γ pr w
   ⊆pr/refl = st (λ x → identity' _) (λ x → identity' _) 

   ⊆pr/wken : ∀{Γ Δ A w} → Δ ⊆ Γ pr w → Δ ⊆ (A at w :: Γ) pr w
   ⊆pr/wken {Γ} {Δ} {B} {w} (st sub sub≺) = st sub' sub≺'  
    where
      sub' : ∀{A w'} → w ≺* w' 
         → A at w' ∈ Δ 
         → (B at w :: Γ) ⇒ A [ w' ]
      sub' ω x = wk (⊆to/wken* ω (⊆to/refl _)) (sub ω x)

      sub≺' : ∀{A w'} → w ≺+ w' 
         → A at w' ∈ (B at w :: Γ) 
         → Δ ⇒ A [ w' ]
      sub≺' ω Z = abort (≺+⊀ ω ≺*≡)
      sub≺' ω (S x) = sub≺ ω x

   ⊆pr/wkenirrev : ∀{Γ Δ A w w'} 
      → w ⊀ w' 
      → Δ ⊆ Γ pr w
      → Δ ⊆ (A at w' :: Γ) pr w
   ⊆pr/wkenirrev {Γ} {Δ} {B} {w} {w''} ω (st sub sub≺) = st sub' sub≺'  
    where
      sub' : ∀{A w'} → w ≺* w' 
         → A at w' ∈ Δ 
         → (B at w'' :: Γ) ⇒ A [ w' ]
      sub' ω' x = wk (⊆to/wkenirrev (ω o ≺*trans ω') (⊆to/refl _)) (sub ω' x)

      sub≺' : ∀{A w'} → w ≺+ w' 
         → A at w' ∈ (B at w'' :: Γ) 
         → Δ ⇒ A [ w' ]
      sub≺' ω' Z = abort (ω (≺*+ ω'))
      sub≺' ω' (S x) = sub≺ ω' x

   ⊆pr/wken* : ∀{Γ Δ A w w'} 
      → w' ≺* w 
      → Δ ⊆ Γ pr w
      → Δ ⊆ (A at w' :: Γ) pr w
   ⊆pr/wken* ≺*≡ = ⊆pr/wken 
   ⊆pr/wken* (≺*+ ω) = ⊆pr/wkenirrev (≺+⊀ ω) 

   ⊆pr/both : ∀{Γ Δ A w} → Δ ⊆ Γ pr w → (A at w :: Δ) ⊆ (A at w :: Γ) pr w
   ⊆pr/both {Γ} {Δ} {B} {w} (st sub sub≺) = st sub' sub≺'  
    where
      sub' : ∀{A w'} → w ≺* w' 
         → A at w' ∈ (B at w :: Δ) 
         → (B at w :: Γ) ⇒ A [ w' ]
      sub' ω Z = identity _
      sub' ω (S x) = wk (⊆to/wken* ω (⊆to/refl _)) (sub ω x)

      sub≺' : ∀{A w'} → w ≺+ w' 
         → A at w' ∈ (B at w :: Γ) 
         → (B at w :: Δ) ⇒ A [ w' ]
      sub≺' ω Z = identity _
      sub≺' ω (S x) = wk (⊆to/wkenirrev (≺+⊀ ω) (⊆to/refl _)) (sub≺ ω x) 
 
   ⊆pr/≺+ : ∀{Γ Δ w w'} → w ≺+ w' → Δ ⊆ Γ pr w → Δ ⊆ Γ pr w'
   ⊆pr/≺+ ω (st sub sub≺) = st 
      (λ ω' → sub (≺*+ (≺+*trans ω ω'))) 
      (λ ω' → sub≺ (≺+trans ω ω'))

   ⊆pr/≺* : ∀{Γ Δ w w'} → w ≺* w' → Δ ⊆ Γ pr w → Δ ⊆ Γ pr w'
   ⊆pr/≺* ω (st sub sub≺) = st 
      (λ ω' → sub (≺*trans ω ω')) 
      (λ ω' → sub≺ (≺*+trans ω ω'))

   ⊆pr/≺+' : ∀{Γ Δ w w'} → w ≺+ w' → Δ ⊆ Γ pr w → Γ ⊆ Δ pr w'
   ⊆pr/≺+' ω (st sub sub≺) = st 
      (λ ω' → sub≺ (≺+*trans ω ω'))
      (λ ω' → sub (≺*+ (≺+trans ω ω')))

