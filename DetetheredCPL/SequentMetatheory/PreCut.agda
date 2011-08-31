-- Constructive Provability Logic 
-- De-tethered intuitionistic variant
-- Robert J. Simmons, Bernardo Toninho

module DetetheredCPL.SequentMetatheory.PreCut where
open import Prelude hiding (⊥)
open import Accessibility.Inductive 
open import Accessibility.IndexedList
open import DetetheredCPL.Core 
open import DetetheredCPL.SequentMetatheory.Core
open import DetetheredCPL.SequentMetatheory.IH

module SEQUENT-PRE-CUT
  (UWF : UpwardsWellFounded 
   ; dec≺ : (w w' : _) → Decidable (TRANS-UWF._≺*_ UWF w w')) where
   open TRANS-UWF UWF
   open ILIST UWF
   open CORE UWF 
   open SEQUENT-CORE UWF dec≺
   open SEQUENT-IH UWF dec≺

   decutP : (wc : W) → ((wc' : W) → wc ≺+ wc' → P wc') → ∀{Γ w A C}
            → Γ ⇒ A [ w ] 
            → Γ ⇒ C [ wc ]
            → A at w :: Γ ⇒ C [ wc ]
   decutP wc ih {w = w} D E with dec≺ wc w
   decutP wc ih D E | Inl ≺*≡ = wk wken E 
   decutP wc ih D E | Inr ω = wk (⊆to/wkenirrev ω (⊆to/refl _)) E
   decutP wc ih D E | Inl (≺*+ ωc) = 
      decut ωc D E
    where 
     mutual 
      decut : ∀{w A Γ C} 
         → wc ≺+ w
         → Γ ⇒ A [ w ]
         → Γ ⇒ C [ wc ]
         → A at w :: Γ ⇒ C [ wc ]
      decut ω D (hyp x) = hyp (S x)
      decut ω D (⊃R D₁) = 
         ⊃R (wk exch (decut ω (wk (⊆to/wkenirrev (≺+⊀ ω) (⊆to/refl _)) D) D₁))
      decut ω D (⊃L ≺*≡ x D₁ D₂) = 
         ⊃L ≺*≡ (S x) (decut ω D D₁) 
          (wk exch (decut ω (wk (⊆to/wkenirrev (≺+⊀ ω) (⊆to/refl _)) D) D₂))
      decut {w} {A} {Γ} ω D (⊃L {B₁} {B₂} {w = w'} (≺*+ ωh) x D₁ D₂) = 
         ⊃L (≺*+ ωh) (S x) (P.decut (ih _ ωh) D D₁) 
          (wk exch (decut ω (D' D₁ x) D₂))
       where
         D' : ∀{w'} → Γ ⇒ B₁ [ w' ] → (B₁ ⊃ B₂) at w' ∈ Γ 
            → B₂ at w' :: Γ ⇒ A [ w ] 
         D' {w'} D₁ x with dec≺ w w'
         D' D₁ x | Inl ≺*≡ = wk wken D
         D' D₁ x | Inl (≺*+ ω') =
            P.decut (ih _ ω) 
             (P.⊃E' (ih _ (≺+trans ω ω')) 
              (P.ident (ih _ (≺+trans ω ω')) x) D₁)
             D
         D' D₁ x | Inr ω = wk (⊆to/wkenirrev ω (⊆to/refl _)) D

      decut ω D (⊥L ωh x) = ⊥L ωh (S x)
      decut ω D (◇R ω' D₁) = ◇R ω' (P.decut (ih _ (≺+0 ω')) D D₁)
      decut ω D (◇L ωh x D₁) = ◇L ωh (S x) 
         λ ω' D₀ → decut ω D (D₁ ω' (P.cut (ih _ (≺*S' ωh ω')) D D₀))
      decut ω D (□R D₁) = □R (λ ω' → P.decut (ih _ (≺+0 ω')) D (D₁ ω'))
      decut ω D (□L ωh x D₁) = □L ωh (S x) 
         λ D₀ → decut ω D (D₁ λ ω' → P.cut (ih _ (≺*S' ωh ω')) D (D₀ ω'))

   extendP : (wc : W) → ((wc' : W) → wc ≺+ wc' → P wc') → ∀{Δ Γ A w} 
            → Δ ⊆ Γ pr wc
            → Δ ⇒ A [ w ] 
            → Δ ⊆ A at w :: Γ pr wc 
   extendP wc ih {Δ} {Γ} {B} {w} (st sub sub≺) D = st sub' sub≺'
    where
      sub' : ∀{A w'} → wc ≺* w' 
         → A at w' ∈ Δ 
         → (B at w :: Γ) ⇒ A [ w' ]
      sub' {A} {w'} ω x with dec≺ w' w 
      sub' ω x | Inl ≺*≡ = wk wken (sub ω x) 
      sub' ω x | Inr ω' = wk (⊆to/wkenirrev ω' (⊆to/refl _)) (sub ω x) 
      sub' ≺*≡ x | Inl (≺*+ ω') = 
         decutP _ ih (P.subst (ih _ ω') (⊆pr/≺+ ω' (st sub sub≺)) D) 
          (sub ≺*≡ x)
      sub' (≺*+ ω) x | Inl (≺*+ ω') = 
         P.decut (ih _ ω) 
          (P.subst (ih _ (≺+trans ω ω')) 
           (⊆pr/≺+ (≺+trans ω ω') (st sub sub≺)) D) 
          (sub (≺*+ ω) x) 

      sub≺' : ∀{A w'} → wc ≺+ w' 
         → A at w' ∈ (B at w :: Γ)
         → Δ ⇒ A [ w' ]
      sub≺' ω Z = D
      sub≺' ω (S x) = sub≺ ω x

   extendbothP : (wc : W) → ((wc' : W) → wc ≺+ wc' → P wc') → ∀{Δ Γ A w} 
            → wc ≺+ w
            → Δ ⊆ Γ pr wc
            → Δ ⇒ A [ w ] 
            → (A at w :: Δ) ⊆ (A at w :: Γ) pr wc 
   extendbothP wc ih {Δ} {Γ} {B} {w} ωA (st sub sub≺) D = st sub' sub≺' 
    where
      sub' : ∀{A w'} → wc ≺* w' 
         → A at w' ∈ (B at w :: Δ) 
         → (B at w :: Γ) ⇒ A [ w' ]
      sub' ω Z = P.subst (ih _ ωA) (⊆pr/wken (⊆pr/≺+ ωA (st sub sub≺))) D
      sub' {A} {w'} ω (S x) with dec≺ w' w 
      sub' ω (S x) | Inl ≺*≡ = wk wken (sub ω x) 
      sub' ω (S x) | Inr ω' = wk (⊆to/wkenirrev ω' (⊆to/refl _)) (sub ω x) 
      sub' ≺*≡ (S x) | Inl (≺*+ ω') = 
         decutP _ ih (P.subst (ih _ ω') (⊆pr/≺+ ω' (st sub sub≺)) D) 
          (sub ≺*≡ x)
      sub' (≺*+ ω) (S x) | Inl (≺*+ ω') = 
         P.decut (ih _ ω) 
          (P.subst (ih _ (≺+trans ω ω')) 
           (⊆pr/≺+ (≺+trans ω ω') (st sub sub≺)) D) 
          (sub (≺*+ ω) x) 

      sub≺' : ∀{A w'} → wc ≺+ w' 
         → A at w' ∈ (B at w :: Γ)
         → (B at w :: Δ) ⇒ A [ w' ]
      sub≺' ω Z = identity _
      sub≺' ω (S x) = P.decut (ih _ ω) D (sub≺ ω x)


   decutMP : (wc : W) → ((wc' : W) → wc ≺+ wc' → P wc') → ∀{Γ Δ w A C s}
            → Δ ⊆ Γ pr wc
            → Γ ⇒ A [ w ] 
            → Δ / Γ ⇒ C [ wc ]/ s
            → Δ / A at w :: Γ ⇒ C [ wc ]/ s
   decutMP wc ih {w = w} sub D E with dec≺ wc w
   decutMP wc ih sub D E | Inl ≺*≡ = wkM wken E 
   decutMP wc ih sub D E | Inr ω = wkM (⊆to/wkenirrev ω (⊆to/refl _)) E
   decutMP wc ih sub D E | Inl (≺*+ ωc) = 
      decut ωc sub D E
    where 
     mutual 
      decut : ∀{w A Δ Γ C s} 
         → wc ≺+ w
         → Δ ⊆ Γ pr wc
         → Γ ⇒ A [ w ]
         → Δ / Γ ⇒ C [ wc ]/ s
         → Δ / A at w :: Γ ⇒ C [ wc ]/ s
      decut ω sub D (hyp x) = hyp (S x)
      decut ω sub D (⊃R D₁) = 
         ⊃R (wkM exch (decut ω (⊆pr/wken sub) 
          (wk (⊆to/wkenirrev (≺+⊀ ω) (⊆to/refl _)) D) D₁))
      decut ω sub D (⊃L x D₁ D₂) = 
         ⊃L (S x) (decut ω sub D D₁) 
          (wkM exch (decut ω (⊆pr/wken sub)
           (wk (⊆to/wkenirrev (≺+⊀ ω) (⊆to/refl _)) D) D₂))
      decut {w} {A} {Δ} {Γ} ω sub D (⊃L+ {B₁} {B₂} {w = w'} ωh x D₁ D₂) = 
         ⊃L+ ωh (S x) D₁
          (wkM exch (decut ω (sub' D₁ x) (D' D₁ x) D₂))
       where
         sub' : ∀{w'} → Δ ⇒ B₁ [ w' ] → (B₁ ⊃ B₂) at w' ∈ Γ 
            → Δ ⊆ B₂ at w' :: Γ pr wc
         sub' {w'} D₁ x with dec≺ wc w'
         sub' D₁ x | Inl ≺*≡ = ⊆pr/wken sub
         sub' D₁ x | Inr ω = ⊆pr/wkenirrev ω sub
         sub' D₁ x | Inl (≺*+ ω') = 
            extendP _ ih sub (P.⊃E' (ih _ ω') (⊆pr/later' ω' sub x) D₁)

         D' : ∀{w'} → Δ ⇒ B₁ [ w' ] → (B₁ ⊃ B₂) at w' ∈ Γ 
            → B₂ at w' :: Γ ⇒ A [ w ] 
         D' {w'} D₁ x with dec≺ w w'
         D' D₁ x | Inl ≺*≡ = wk wken D
         D' D₁ x | Inr ω = wk (⊆to/wkenirrev ω (⊆to/refl _)) D
         D' D₁ x | Inl (≺*+ ω') =
            P.decut (ih _ ω) 
             (P.⊃E' (ih _ (≺+trans ω ω')) 
              (P.ident (ih _ (≺+trans ω ω')) x)
              (P.subst (ih _ (≺+trans ω ω')) (⊆pr/≺+ (≺+trans ω ω') sub) D₁))
             D 

      decut ω sub D (⊥L ωh x) = ⊥L ωh (S x)
      decut ω sub D (◇R ω' D₁) = ◇R ω' D₁ -- P.decut (ih _ (≺+0 ω')) D D₁
      decut ω sub D (◇L ωh x D₁) = ◇L ωh (S x) 
         λ ω' D₀ → decut ω sub D (D₁ ω' D₀)
      decut ω sub D (□R D₁) = □R D₁
      decut ω sub D (□L ωh x D₁) = □L ωh (S x) 
         λ D₀ → decut ω sub D (D₁ D₀)

   m→P : (wc : W) → ((wc' : W) → wc ≺+ wc' → P wc') → ∀{Γ Δ A s}  
            → Δ ⊆ Γ pr wc 
            → Δ / Γ ⇒ A [ wc ]/ s
            → Γ ⇒ A [ wc ] 
   m→P wc ih = m→ 
    where 
      m→ : ∀{Γ Δ A s}  
            → Δ ⊆ Γ pr wc 
            → Δ / Γ ⇒ A [ wc ]/ s
            → Γ ⇒ A [ wc ] 
      m→ sub (hyp x) = hyp x
      m→ sub (⊃R D₁) = ⊃R (m→ (⊆pr/wken sub) D₁)
      m→ sub (⊃L x D₁ D₂) = ⊃L ≺*≡ x (m→ sub D₁) (m→ (⊆pr/wken sub) D₂)
      m→ sub (⊃L+ ωh x D₁ D₂) = 
         ⊃L (≺*+ ωh) x (P.subst (ih _ ωh) (⊆pr/≺+ ωh sub) D₁) 
          (m→ (extendP _ ih sub (P.⊃E' (ih _ ωh) (⊆pr/later' ωh sub x) D₁)) 
           D₂)
      m→ sub (⊥L ωh x) = ⊥L ωh x
      m→ sub (◇R ω D₁) = 
         ◇R ω (P.subst (ih _ (≺+0 ω)) (⊆pr/≺+ (≺+0 ω) sub) D₁) -- ◇R ω D₁
      m→ sub (◇L ωh x D₁) = ◇L ωh x 
         λ ω D₀ → m→ sub 
          (D₁ ω (P.subst (ih _ (≺*S' ωh ω)) (⊆pr/≺+' (≺*S' ωh ω) sub) D₀))
      m→ sub (□R D₁) = □R 
         λ ω → P.subst (ih _ (≺+0 ω)) (⊆pr/≺+ (≺+0 ω) sub) (D₁ ω)
      m→ sub (□L ωh x D₁) = □L ωh x 
         λ D₀ → m→ sub (D₁ 
         λ ω → P.subst (ih _ (≺*S' ωh ω)) (⊆pr/≺+' (≺*S' ωh ω) sub) (D₀ ω))

   →mP : (wc : W) → ((wc' : W) → wc ≺+ wc' → P wc') → ∀{Γ Δ A} 
            → Δ ⊆ Γ pr wc 
            → Γ ⇒ A [ wc ] 
            → ∃ λ s → Δ / Γ ⇒ A [ wc ]/ s
   →mP wc ih sub D = →m sub D 
    where 
      →m : ∀{Γ Δ A} → Δ ⊆ Γ pr wc → Γ ⇒ A [ wc ] 
         → ∃ λ s → Δ / Γ ⇒ A [ wc ]/ s
      →m sub (hyp x) = , hyp x
      →m sub (⊃R D₁) = , ⊃R (snd (→m (⊆pr/wken sub) D₁))
      →m sub (⊃L ≺*≡ x D₁ D₂) = , 
         ⊃L x (snd (→m sub D₁)) (snd (→m (⊆pr/wken sub) D₂))
      →m {Γ} sub (⊃L (≺*+ ωh) x D₁ D₂) = , 
         ⊃L+ ωh x E₁ (snd (→m (extendP _ ih sub E₂) D₂))
       where
         E₁ = P.subst (ih _ ωh) (⊆pr/≺+' ωh sub) D₁
         E₂ = P.⊃E' (ih _ ωh) (⊆pr/later' ωh sub x) E₁
      →m sub (⊥L ωh x) = , ⊥L ωh x
      →m sub (◇R ω D₁) = , 
         ◇R ω (P.subst (ih _ (≺+0 ω)) (⊆pr/≺+' (≺+0 ω) sub) D₁) -- D₁
      →m {Γ} sub (◇L ωh x D₁) = , ◇L ωh x 
         λ ω D₀ → snd (→m sub (D₁ ω 
          (P.subst (ih _ (≺*S' ωh ω)) (⊆pr/≺+ (≺*S' ωh ω) sub) D₀))) 
      →m sub (□R D₁) = , □R 
         λ ω → P.subst (ih _ (≺+0 ω)) (⊆pr/≺+' (≺+0 ω) sub) (D₁ ω)
      →m sub (□L ωh x D₁) = , □L ωh x 
         λ D₀ → snd (→m sub (D₁ 
          λ ω → P.subst (ih _ (≺*S' ωh ω)) (⊆pr/≺+ (≺*S' ωh ω) sub) (D₀ ω)))