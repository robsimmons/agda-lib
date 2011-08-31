-- Constructive Provability Logic 
-- De-tethered intuitionistic variant
-- Robert J. Simmons, Bernardo Toninho

module DetetheredCPL.SequentMetatheory.PostCut where
open import Prelude hiding (⊥)
open import Accessibility.Inductive 
open import Accessibility.IndexedList
open import DetetheredCPL.Core 
open import DetetheredCPL.SequentMetatheory.Core
open import DetetheredCPL.SequentMetatheory.IH
open import DetetheredCPL.SequentMetatheory.PreCut
-- open import UntetheredCPL.SequentMetatheory.Cut -- "Real" version
open import DetetheredCPL.SequentMetatheory.CutAxiom -- "Fake" version

module SEQUENT-POST-CUT
  (UWF : UpwardsWellFounded 
   ; dec≺ : (w w' : _) → Decidable (TRANS-UWF._≺*_ UWF w w')) where
   open TRANS-UWF UWF
   open ILIST UWF
   open CORE UWF 
   open SEQUENT-CORE UWF dec≺
   open SEQUENT-IH UWF dec≺
   open SEQUENT-PRE-CUT UWF dec≺
   open SEQUENT-CUT UWF dec≺

   ⊃EP : (wc : W) → ((wc' : W) → wc ≺+ wc' → P wc') → ∀{Δ A B} 
            → Δ ⇒ A ⊃ B [ wc ]
            → Δ ⇒ A [ wc ] 
            → Δ ⇒ B [ wc ]
   ⊃EP wc ih D₁ D₂ = cutP _ ih D₁ (⊃L ≺*≡ Z (wk wken D₂) (identity _))

   ⊥EP : (wc : W) → ((wc' : W) → wc ≺+ wc' → P wc') → ∀{Δ A w} 
            → wc ≺* w
            → Δ ⇒ ⊥ [ w ]
            → Δ ⇒ A [ wc ]
   ⊥EP wc ih ω D = cutP _ ih D (⊥L ω Z)

   ◇EP : (wc : W) → ((wc' : W) → wc ≺+ wc' → P wc') → ∀{Δ A C w} 
            → wc ≺* w
            → Δ ⇒ ◇ A [ w ]
            → (∀{w'} → w ≺ w' → Δ ⇒ A [ w' ] → Δ ⇒ C [ wc ])
            → Δ ⇒ C [ wc ] 
   ◇EP wc ih ω D₁ D₂ = cutP _ ih D₁ (◇L ω Z 
      λ ω' D₀ → decutP _ ih D₁ (D₂ ω' (P.cut (ih _ (≺*S' ω ω')) D₁ D₀)))

   □EP : (wc : W) → ((wc' : W) → wc ≺+ wc' → P wc') → ∀{Δ A C w} 
            → wc ≺* w
            → Δ ⇒ □ A [ w ]
            → ((∀{w'} → w ≺ w' → Δ ⇒ A [ w' ]) → Δ ⇒ C [ wc ])
            → Δ ⇒ C [ wc ] 
   □EP wc ih ω D₁ D₂ = cutP _ ih D₁ (□L ω Z 
      λ D₀ → decutP _ ih D₁ (D₂ λ ω' → P.cut (ih _ (≺*S' ω ω')) D₁ (D₀ ω')))

   substP : (wc : W) → ((wc' : W) → wc ≺+ wc' → P wc') → ∀{A Δ Γ} 
            → Δ ⊆ Γ pr wc 
            → Δ ⇒ A [ wc ] 
            → Γ ⇒ A [ wc ]
   substP wc ih = subst -- ⊑to 
    where
      subst : ∀{A Δ Γ} → Δ ⊆ Γ pr wc → Δ ⇒ A [ wc ] → Γ ⇒ A [ wc ]
      subst sub (hyp x) = ⊆pr/now sub x
      subst sub (⊃R D₁) = ⊃R (subst (⊆pr/both sub) D₁)
      subst sub (⊃L ≺*≡ x D₁ D₂) = 
         cutP _ ih 
          (⊃EP _ ih (⊆pr/now sub x) (subst sub D₁)) 
          (subst (⊆pr/both sub) D₂)
      subst sub (⊃L (≺*+ ωh) x D₁ D₂) = 
         cutP _ ih 
          DB
          (subst (extendbothP _ ih ωh sub DB') D₂) 
       where
         DA = P.subst (ih _ ωh) (⊆pr/≺+ ωh sub) D₁
         DB = P.⊃E' (ih _ ωh) (⊆pr/later ωh sub x) DA
         DB' = P.subst (ih _ ωh) (⊆pr/≺+' ωh sub) DB 
      subst sub (⊥L ωh x) = ⊥EP _ ih ωh (⊆pr/soon ωh sub x)
      subst sub (◇R ω D₁) = 
         ◇R ω (P.subst (ih _ (≺+0 ω)) (⊆pr/≺+ (≺+0 ω) sub) D₁)
      subst sub (◇L ωh x D₁) = 
         ◇EP _ ih ωh (⊆pr/soon ωh sub x) 
          λ ω' D₀ → subst sub 
           (D₁ ω' (P.subst (ih _ (≺*S' ωh ω')) 
            (⊆pr/≺+' (≺*S' ωh ω') sub) D₀))
      subst sub (□R D₁) = 
         □R (λ ω → P.subst (ih _ (≺+0 ω)) (⊆pr/≺+ (≺+0 ω) sub) (D₁ ω)) 
      subst sub (□L ωh x D₁) = □EP _ ih ωh (⊆pr/soon ωh sub x) 
         λ D₀ → subst sub 
          (D₁ λ ω' → P.subst (ih _ (≺*S' ωh ω')) 
           (⊆pr/≺+' (≺*S' ωh ω') sub) (D₀ ω'))

   tying-the-knot : (wc : W) → ((wc' : W) → wc ≺+ wc' → P wc') → P wc
   tying-the-knot wc ih = record {
      ident = λ x → identity' _ x ;
      cut = cutP wc ih;
      decut = decutP wc ih;
      decutM = decutMP wc ih;
      extend = extendP wc ih;
      subst = substP wc ih;
      →m = →mP wc ih;
      m→ = m→P wc ih;
      ⊃E' = ⊃EP wc ih;
      ⊥E' = ⊥EP wc ih;
      ◇E' = ◇EP wc ih }

   cut-thms : ∀{wc} → P wc
   cut-thms {wc} = ind+ P 
      (λ wc ih → record {
         ident = λ x → identity' _ x;
         cut = cutP wc ih;
         decut = decutP wc ih;
         decutM = decutMP wc ih;
         extend = extendP wc ih;
         subst = substP wc ih;
         →m = →mP wc ih;
         m→ = m→P wc ih;
         ⊃E' = ⊃EP wc ih;
         ⊥E' = ⊥EP wc ih;
         ◇E' = ◇EP wc ih }) wc