-- Constructive Provability Logic 
-- De-tethered intuitionstic variant
-- Robert J. Simmons, Bernardo Toninho

-- Equivalence of sequent calculus and natural deduction

open import Prelude hiding (⊥)
open import Accessibility.Inductive
open import Accessibility.IndexedList
open import DetetheredCPL.Core renaming (Type to UType)
open import DetetheredCPL.NatDeduction
open import FocusedCPL.Core
open import FocusedCPL.Weakening
open import FocusedCPL.Atomic
open import FocusedCPL.Cut
open import FocusedCPL.Identity
-- open import DetetheredCPL.Sequent

module DetetheredCPL.Equiv where

module EQUIV 
  (UWF : UpwardsWellFounded)
  (dec≺ : (w w' : _) → Decidable (TRANS-UWF._≺*_ UWF w w')) where
  open TRANS-UWF UWF
  open ILIST UWF
  open CORE UWF renaming (MCtx to UMCtx)
  open NAT-DEDUCTION UWF hiding (wkN)
  open SEQUENT UWF
  open WEAKENING UWF
  open ATOMIC UWF
  open CUT UWF dec≺
  open IDENTITY UWF dec≺

  pol⁺ : UType → Type ⁺
  pol⁻ : UType → Type ⁻

  pol⁺ (a Q ⁺) = a Q ⁺
  pol⁺ ⊥ = ⊥
  pol⁺ (◇ A) = ◇ (pol⁺ A)
  pol⁺ (□ A) = □ (pol⁺ A)
  pol⁺ (a Q ⁻) = ↓ (a Q ⁻)
  pol⁺ (A ⊃ B) = ↓ (pol⁺ A ⊃ pol⁻ B)

  pol⁻ (a Q ⁺) = ↑ (a Q ⁺)
  pol⁻ ⊥ = ↑ ⊥
  pol⁻ (◇ A) = ↑ (◇ (pol⁺ A))
  pol⁻ (□ A) = ↑ (□ (pol⁺ A))
  pol⁻ (a Q ⁻) = a Q ⁻
  pol⁻ (A ⊃ B) = pol⁺ A ⊃ pol⁻ B

  polhyp : Item UType → Item (Type ⁺)
  polhyp (a Q ⁺ at w) = a Q ⁺ at w
  polhyp (⊥ at w) = ↓ (↑ ⊥) at w
  polhyp (◇ A at w) = ↓ (↑ (◇ (pol⁺ A))) at w
  polhyp (□ A at w) = ↓ (↑ (□ (pol⁺ A))) at w
  polhyp (a Q ⁻ at w) = ↓ (a Q ⁻) at w
  polhyp ((A ⊃ B) at w) = ↓ (pol⁺ A ⊃ pol⁻ B) at w

  polΓ : UMCtx → MCtx
  polΓ [] = []
  polΓ (Item :: Γ) = polhyp Item :: polΓ Γ

  polx : ∀{Item Γ} → Item ∈ Γ → (polhyp Item) ∈ (polΓ Γ)
  polx Z = Z
  polx (S x) = S (polx x)

  Pfoc : W → Set
  Pfoc wc = ∀{A Γ}
    → Γ ⊢ A [ wc ]
    → Term [] (polΓ Γ) wc · (Reg (pol⁻ A))

  PdefocN : W → Set
  PdefocN wc = ∀{Γ A}
    → Term [] (polΓ Γ) wc · (Reg (↑ (pol⁺ A)))
    → Γ ⊢ A [ wc ]
  


{-
  PdefocV : W → Set
  PdefocV wc = ∀{Γ A}
    → Value [] Γ wc A
    → eraseΓ Γ ⊢ eraseA A [ wc ]


  PdefocSp : W → Set
  PdefocSp wc = ∀{Γ B A wh}
    → Γ stableΓ
    → wc ≺* wh
    → eraseΓ Γ ⊢ eraseA B [ wh ]
    → Spine [] Γ wh B wc (Reg A)
    → eraseΓ Γ ⊢ eraseA A [ wc ]


  eraseΩ : ICtx → UMCtx
  eraseΩ · = []
  eraseΩ (I A w) = [ eraseA A at w ]

  eraseΓ : MCtx → UMCtx
  eraseΓ [] = []
  eraseΓ ((A at w) :: Γ) = (eraseA A at w) :: eraseΓ Γ


  _stableΓ : MCtx → Set
  _stableΓ = LIST.All (λ Item → prjx Item stable⁺)

  unerasex : ∀{Γ A w} 
    → Γ stableΓ
    → (A at w) ∈ eraseΓ Γ 
    → (∃ λ B → ((↓ B at w) ∈ Γ) × (A ≡ eraseA B))
      + (∃ λ Q → ((a Q ⁺ at w) ∈ Γ) × (A ≡ a Q ⁺))
  unerasex {[]} pf ()
  unerasex {A :: xs} pf Z with pf Z 
  unerasex {(a Q .⁺ at w) :: xs} pf Z | pf' = Inr (_ , Z , refl)
  unerasex {(↓ A at w) :: xs} pf Z | pf' = Inl (_ , Z , refl)
  unerasex {(⊥ at w) :: xs} pf Z | ()
  unerasex {(◇ A at w) :: xs} pf Z | ()
  unerasex {(□ A at w) :: xs} pf Z | ()
  unerasex {_ :: _} pf (S x) with unerasex (λ x' → pf (S x')) x
  ... | Inl (_ , x' , refl) = Inl (_ , S x' , refl)
  ... | Inr (_ , x' , refl) = Inr (_ , S x' , refl)

-}

  record Pequiv (wc : W) : Set where
   field
    foc : Pfoc wc
    defocN : PdefocN wc
{-
    defocV : PdefocV wc
    defocN : PdefocN wc
    defocSp : PdefocSp wc
-}

  module EQUIV-LEM (wc : W) (ih : (wc' : W) → wc ≺+ wc' → Pequiv wc') where

{-
    defocV : PdefocV wc
    defocN : PdefocN wc
    defocSp : PdefocSp wc

    defocV pf (pR x) = hyp (erasex x)
    defocV pf (↓R N₁) = defocN pf N₁
    defocV pf (◇R ω N₁) = ◇I ω (Pequiv.defocN (ih _ (≺+0 ω)) pf N₁)
    defocV pf (□R N₁) = □I λ ω → Pequiv.defocN (ih _ (≺+0 ω)) pf (N₁ ω)

    defocN pf (↓L pf⁻ ωh x Sp) = defocSp pf ωh (hyp (erasex x)) Sp
    defocN pf (↑R V₁) = defocV pf V₁
    defocN pf (⊃R (L pf⁺ N₁)) = ⊃I (defocN (LIST.ALL.cons pf⁺ pf) N₁)
    defocN pf (⊃R ⊥L) = ⊃I (⊥E ≺*≡ (hyp Z))
    defocN pf (⊃R (◇L N₁)) =
      ⊃I (◇E ≺*≡ (hyp Z)
           λ ω D₀ →
             WK-N.wkN wken
               (defocN pf
                 (N₁ ω 
                   (Pequiv.foc (ih _ (≺+0 ω)) pf (WK-N.wkN (wkto ω) D₀)))))
    defocN pf (⊃R (□L N₁)) = 
      ⊃I (□E ≺*≡ (hyp Z) 
           λ D₀ → 
             WK-N.wkN wken 
               (defocN pf 
                 (N₁ λ ω → 
                       Pequiv.foc (ih _ (≺+0 ω)) pf 
                         (WK-N.wkN (wkto ω) (D₀ ω)))))
 
    defocSp pf ω R pL = R 
    defocSp pf ω R (↑L (L pf⁺ N₁)) = 
      subst ω R (defocN (LIST.ALL.cons pf⁺ pf) N₁)
    defocSp pf ω R (↑L ⊥L) = ⊥E ω R
    defocSp pf ω R (↑L (◇L N₁)) = 
      ◇E ω R
        λ ω' D₀ → defocN pf (N₁ ω' (Pequiv.foc (ih _ (≺*S' ω ω')) pf D₀))
    defocSp pf ω R (↑L (□L N₁)) = 
      □E ω R 
        λ D₀ → defocN pf (N₁ λ ω' → Pequiv.foc (ih _ (≺*S' ω ω')) pf (D₀ ω'))
    defocSp pf ω R (⊃L V₁ Sp₂) with ω
    ... | ≺*≡ = defocSp pf ω (⊃E R (defocV pf V₁)) Sp₂ 
    ... | ≺*+ ω' = 
      defocSp pf ω (⊃E R (Pequiv.defocV (ih _ ω') pf V₁)) Sp₂ 
-}

    u↓↑E : ∀{A w Γ}
      → Term [] Γ w · (Reg (↑ (↓ A)))
      → Term [] Γ w · (Reg A)
    u↓↑E N = cut N (expand⁻ (↓L <> ≺*≡ Z (↑L (L <> (↓L <> ≺*≡ Z hyp⁻)))))

    u⊃I : ∀{A B w Γ}
      → Term [] ((polhyp (A at w)) :: Γ) w · (Reg B)
      → Term [] Γ w · (Reg (pol⁺ A ⊃ B))
    u⊃I {a Q ⁺} N = ⊃R (L <> N)
    u⊃I {⊥} N = ⊃R ⊥L
    u⊃I {◇ A} N = 
      cut (⊃R (L <> N)) 
        (⊃R (◇L λ ω N₀ → 
                  expand⁻ (↓L <> ≺*≡ Z (⊃L (↓R (↑R (◇R ω N₀))) hyp⁻))))
    u⊃I {□ A} N = 
      cut (⊃R (L <> N)) 
        (⊃R (□L λ N₀ →  
                  expand⁻ (↓L <> ≺*≡ Z (⊃L (↓R (↑R (□R λ ω → N₀ ω))) hyp⁻))))
    u⊃I {a Q ⁻} N = ⊃R (L <> N)
    u⊃I {A ⊃ B} N = ⊃R (L <> N)

    u⊃E : ∀{A B w Γ}
      → Term [] Γ w · (Reg (pol⁺ A ⊃ B))
      → Term [] Γ w · (Reg (pol⁻ A))
      → Term [] Γ w · (Reg B)
    u⊃E {a Q ⁺} N M = 
      cut M 
        (cut (wkN <> wken · N) 
          (expand⁻ (↓L <> ≺*≡ (S Z) (↑L (L <> 
                     (↓L <> ≺*≡ (S Z) (⊃L (pR Z) hyp⁻)))))))
    u⊃E {⊥} N M = cut M (expand⁻ (↓L <> ≺*≡ Z (↑L ⊥L)))
    u⊃E {◇ A} N M = 
      cut M 
        (cut (wkN <> wken · N) 
          (expand⁻ (↓L <> ≺*≡ (S Z) (↑L (◇L 
                     λ ω N₀ → ↓L <> ≺*≡ Z (⊃L (◇R ω N₀) hyp⁻))))))
    u⊃E {□ A} N M = 
      cut M 
        (cut (wkN <> wken · N) 
          (expand⁻ (↓L <> ≺*≡ (S Z) (↑L (□L 
                     λ N₀ → ↓L <> ≺*≡ Z (⊃L (□R (λ ω → N₀ ω)) hyp⁻))))))
    u⊃E {a Q ⁻} N M = 
      cut N (expand⁻ (↓L <> ≺*≡ Z (⊃L (↓R (wkN <> wken · M)) hyp⁻)))
    u⊃E {A ⊃ B} N M = 
      cut N (expand⁻ (↓L <> ≺*≡ Z (⊃L (↓R (wkN <> wken · M)) hyp⁻)))

    u⊥E : ∀{A w wc Γ}
      → wc ≺* w
      → Term [] Γ w · (Reg (↑ ⊥))
      → Term [] Γ wc · (Reg A)
    u⊥E ω N = u↓↑E (subst⁻ <> ω N (↑L ⊥L))

    u◇E : ∀{A w wc Γ C}
      → wc ≺* w
      → Term [] Γ w · (Reg (↑ (◇ A)))
      → (∀{w'} → w ≺ w' → Term [] Γ w' · (Reg (↑ A)) → Term [] Γ wc · (Reg C))
      → Term [] Γ wc · (Reg C)
    u◇E ω N₁ N₂ =
      u↓↑E (cut N₁ 
             (↓L <> ω Z 
               (↑L (◇L (λ ω' N₀ → ↑R (↓R (decut N₁ (N₂ ω' (cut N₁ N₀)))))))))

    foc : Pfoc wc
    foc* : ∀{A Γ w}
      → wc ≺* w
      → Γ ⊢ A [ w ]
      → Term [] (polΓ Γ) w · (Reg (pol⁻ A))
    foc* ≺*≡ N = foc N
    foc* (≺*+ ω) N = Pequiv.foc (ih _ ω) N

    foc {a N ⁻} (hyp x) = ↓L <> ≺*≡ (polx x) pL
    foc {a N ⁺} (hyp x) = ↑R (pR (polx x))
    foc {⊥} (hyp x) = expand⁻ (↓L <> ≺*≡ (polx x) hyp⁻)
    foc {A ⊃ B} (hyp x) = expand⁻ (↓L <> ≺*≡ (polx x) hyp⁻)
    foc {◇ A} (hyp x) = expand⁻ (↓L <> ≺*≡ (polx x) hyp⁻)
    foc {□ A} (hyp x) = expand⁻ (↓L <> ≺*≡ (polx x) hyp⁻)
    foc {A ⊃ B} (⊃I D₁) = u⊃I {A} {pol⁻ B} (foc D₁)
    foc {B} (⊃E {A = A} D₁ D₂) = u⊃E {A} (foc D₁) (foc D₂) 
    foc (⊥E ω D₁) = u↓↑E (rsubstN [] ω (foc* ω D₁) (↓L <> ω Z (↑L ⊥L)) ·t)
    foc {◇ (a N ⁺)} (◇I ω D₁) = ↑R (◇R ω (Pequiv.foc (ih _ (≺+0 ω)) D₁))
    foc {◇ ⊥} (◇I ω D₁) = ↑R (◇R ω (Pequiv.foc (ih _ (≺+0 ω)) D₁))
    foc {◇ (◇ A)} (◇I ω D₁) = ↑R (◇R ω (Pequiv.foc (ih _ (≺+0 ω)) D₁))
    foc {◇ (□ A)} (◇I ω D₁) = ↑R (◇R ω (Pequiv.foc (ih _ (≺+0 ω)) D₁)) -- 
    foc {◇ (a N ⁻)} (◇I ω D₁) = 
      ↑R (◇R ω (↑R (↓R (Pequiv.foc (ih _ (≺+0 ω)) D₁))))
    foc {◇ (A ⊃ B)} (◇I ω D₁) = 
      ↑R (◇R ω (↑R (↓R (Pequiv.foc (ih _ (≺+0 ω)) D₁))))
    foc {C} (◇E ωh D₁ D₂) = 
      u◇E ωh (foc* ωh D₁)
        λ ω N₀ → foc (D₂ ω (Pequiv.defocN (ih _ (≺*S' ωh ω)) N₀))
    foc (□I D₁) = {!!}
    foc (□E ωh D₁ D₂) = {!!}
{-
    foc {↑ (↓ A)} pf D = ↑R (↓R (foc {A} pf D))
    foc {↑ (◇ A)} pf (◇I ω D₁) = ↑R (◇R ω (Pequiv.foc (ih _ (≺+0 ω)) pf D₁))
    foc {↑ (□ A)} pf (□I D₁) = 
      ↑R (□R λ ω → Pequiv.foc (ih _ (≺+0 ω)) pf (D₁ ω))
    foc {a Q .⁺ ⊃ B} pf (⊃I D₁) = ⊃R (L <> (foc (LIST.ALL.cons <> pf) D₁))
    foc {↓ A ⊃ B} pf (⊃I D₁) = ⊃R (L <> (foc (LIST.ALL.cons <> pf) D₁))
    foc {⊥ ⊃ B} pf (⊃I D₁) = ⊃R ⊥L
    foc {◇ A ⊃ B} pf (⊃I D₁) = u◇⊃I (foc (LIST.ALL.cons <> pf) D₁) 
    foc {□ A ⊃ B} pf (⊃I D₁) = u□⊃I (foc (LIST.ALL.cons <> pf) D₁)

    foc {A} pf (hyp x) = {!!}

    foc {A} pf (CORE.⊃E {B} D₁ D₂) = {!!}
    foc pf (⊥E ω D₁) with ω
    ... | ≺*≡ = u⊥E ω (foc pf D₁)
    ... | ≺*+ ω' = u⊥E ω (Pequiv.foc (ih _ ω') pf D₁) 
    foc pf (◇E ≺*≡ D₁ D₂) = {!!}
    foc pf (◇E (≺*+ y) D₁ D₂) = {!!}
    foc pf (□E ≺*≡ D₁ D₂) = {!!}
    foc pf (□E (≺*+ y) D₁ D₂) = {!!}
-}


{-
  eraseA : ∀{⁼} → Type ⁼ → UType
  eraseA {⁼} (a Q .⁼) = a Q ⁼
  eraseA (↓ A) = eraseA A
  eraseA ⊥ = ⊥
  eraseA (◇ A) = ◇ (eraseA A)
  eraseA (□ A) = □ (eraseA A)
  eraseA (↑ A) = eraseA A
  eraseA (A ⊃ B) = eraseA A ⊃ eraseA B

  eraseΩ : ICtx → UMCtx
  eraseΩ · = []
  eraseΩ (I A w) = [ eraseA A at w ]

  eraseΓ : MCtx → UMCtx
  eraseΓ [] = []
  eraseΓ ((A at w) :: Γ) = (eraseA A at w) :: eraseΓ Γ

  erasex : ∀{A w Γ} → (A at w) ∈ Γ → (eraseA A at w) ∈ eraseΓ Γ
  erasex Z = Z
  erasex (S x) = S (erasex x)

  _stableΓ : MCtx → Set
  _stableΓ = LIST.All (λ Item → prjx Item stable⁺)

  unerasex : ∀{Γ A w} 
    → Γ stableΓ
    → (A at w) ∈ eraseΓ Γ 
    → (∃ λ B → ((↓ B at w) ∈ Γ) × (A ≡ eraseA B))
      + (∃ λ Q → ((a Q ⁺ at w) ∈ Γ) × (A ≡ a Q ⁺))
  unerasex {[]} pf ()
  unerasex {A :: xs} pf Z with pf Z 
  unerasex {(a Q .⁺ at w) :: xs} pf Z | pf' = Inr (_ , Z , refl)
  unerasex {(↓ A at w) :: xs} pf Z | pf' = Inl (_ , Z , refl)
  unerasex {(⊥ at w) :: xs} pf Z | ()
  unerasex {(◇ A at w) :: xs} pf Z | ()
  unerasex {(□ A at w) :: xs} pf Z | ()
  unerasex {_ :: _} pf (S x) with unerasex (λ x' → pf (S x')) x
  ... | Inl (_ , x' , refl) = Inl (_ , S x' , refl)
  ... | Inr (_ , x' , refl) = Inr (_ , S x' , refl)

  Pfoc : W → Set
  Pfoc wc = ∀{A Γ}
    → Γ stableΓ
    → eraseΓ Γ ⊢ eraseA A [ wc ]
    → Term [] Γ wc · (Reg A)

  PdefocV : W → Set
  PdefocV wc = ∀{Γ A}
    → Γ stableΓ
    → Value [] Γ wc A
    → eraseΓ Γ ⊢ eraseA A [ wc ]

  PdefocN : W → Set
  PdefocN wc = ∀{Γ A}
    → Γ stableΓ
    → Term [] Γ wc · (Reg A)
    → eraseΓ Γ ⊢ eraseA A [ wc ]

  PdefocSp : W → Set
  PdefocSp wc = ∀{Γ B A wh}
    → Γ stableΓ
    → wc ≺* wh
    → eraseΓ Γ ⊢ eraseA B [ wh ]
    → Spine [] Γ wh B wc (Reg A)
    → eraseΓ Γ ⊢ eraseA A [ wc ]

  record Pequiv (wc : W) : Set where
   field
    foc : Pfoc wc
    defocV : PdefocV wc
    defocN : PdefocN wc
    defocSp : PdefocSp wc

  module EQUIV-LEM (wc : W) (ih : (wc' : W) → wc ≺+ wc' → Pequiv wc') where

    defocV : PdefocV wc
    defocN : PdefocN wc
    defocSp : PdefocSp wc

    defocV pf (pR x) = hyp (erasex x)
    defocV pf (↓R N₁) = defocN pf N₁
    defocV pf (◇R ω N₁) = ◇I ω (Pequiv.defocN (ih _ (≺+0 ω)) pf N₁)
    defocV pf (□R N₁) = □I λ ω → Pequiv.defocN (ih _ (≺+0 ω)) pf (N₁ ω)

    defocN pf (↓L pf⁻ ωh x Sp) = defocSp pf ωh (hyp (erasex x)) Sp
    defocN pf (↑R V₁) = defocV pf V₁
    defocN pf (⊃R (L pf⁺ N₁)) = ⊃I (defocN (LIST.ALL.cons pf⁺ pf) N₁)
    defocN pf (⊃R ⊥L) = ⊃I (⊥E ≺*≡ (hyp Z))
    defocN pf (⊃R (◇L N₁)) =
      ⊃I (◇E ≺*≡ (hyp Z)
           λ ω D₀ →
             WK-N.wkN wken
               (defocN pf
                 (N₁ ω 
                   (Pequiv.foc (ih _ (≺+0 ω)) pf (WK-N.wkN (wkto ω) D₀)))))
    defocN pf (⊃R (□L N₁)) = 
      ⊃I (□E ≺*≡ (hyp Z) 
           λ D₀ → 
             WK-N.wkN wken 
               (defocN pf 
                 (N₁ λ ω → 
                       Pequiv.foc (ih _ (≺+0 ω)) pf 
                         (WK-N.wkN (wkto ω) (D₀ ω)))))
 
    defocSp pf ω R pL = R 
    defocSp pf ω R (↑L (L pf⁺ N₁)) = 
      subst ω R (defocN (LIST.ALL.cons pf⁺ pf) N₁)
    defocSp pf ω R (↑L ⊥L) = ⊥E ω R
    defocSp pf ω R (↑L (◇L N₁)) = 
      ◇E ω R
        λ ω' D₀ → defocN pf (N₁ ω' (Pequiv.foc (ih _ (≺*S' ω ω')) pf D₀))
    defocSp pf ω R (↑L (□L N₁)) = 
      □E ω R 
        λ D₀ → defocN pf (N₁ λ ω' → Pequiv.foc (ih _ (≺*S' ω ω')) pf (D₀ ω'))
    defocSp pf ω R (⊃L V₁ Sp₂) with ω
    ... | ≺*≡ = defocSp pf ω (⊃E R (defocV pf V₁)) Sp₂ 
    ... | ≺*+ ω' = 
      defocSp pf ω (⊃E R (Pequiv.defocV (ih _ ω') pf V₁)) Sp₂ 

    u↓↑E : ∀{A w Γ}
      → Term [] Γ w · (Reg (↑ (↓ A)))
      → Term [] Γ w · (Reg A)
    u↓↑E N = 
      rsubstN [] ≺*≡ N 
        (expand⁻ (↓L <> ≺*≡ Z (↑L (L <> (↓L <> ≺*≡ Z hyp⁻))))) ·t

    u◇⊃I : ∀{A B w Γ}
      → Term [] ((↓ (↑ (◇ A)) at w) :: Γ) w · (Reg B)
      → Term [] Γ w · (Reg (◇ A ⊃ B))
    u◇⊃I N = 
      rsubstN [] ≺*≡ (⊃R (L <> N)) 
        (⊃R (◇L λ ω N₀ → 
                  expand⁻ (↓L <> ≺*≡ Z (⊃L (↓R (↑R (◇R ω N₀))) hyp⁻)))) ·t

    u□⊃I : ∀{A B w Γ}
      → Term [] ((↓ (↑ (□ A)) at w) :: Γ) w · (Reg B)
      → Term [] Γ w · (Reg (□ A ⊃ B))
    u□⊃I N = 
      rsubstN [] ≺*≡ (⊃R (L <> N)) 
        (⊃R (□L λ N₀ →  
                  expand⁻ (↓L <> ≺*≡ Z (⊃L (↓R (↑R (□R λ ω → N₀ ω))) hyp⁻))))
        ·t

    u⊥E : ∀{A w wc Γ}
      → wc ≺* w
      → Term [] Γ w · (Reg (↑ ⊥))
      → Term [] Γ wc · (Reg A)
    u⊥E ω N = u↓↑E (subst⁻ <> ω N (↑L ⊥L))

    u◇E : ∀{A w wc Γ}
      → wc ≺* w
      → Term [] Γ w · (Reg (↑ ⊥))
      → Term [] Γ wc · (Reg A)
    u◇E ω N = u↓↑E (subst⁻ <> ω N (↑L ⊥L))

    foc : Pfoc wc
    foc {↑ (↓ A)} pf D = ↑R (↓R (foc {A} pf D))
    foc {↑ (◇ A)} pf (◇I ω D₁) = ↑R (◇R ω (Pequiv.foc (ih _ (≺+0 ω)) pf D₁))
    foc {↑ (□ A)} pf (□I D₁) = 
      ↑R (□R λ ω → Pequiv.foc (ih _ (≺+0 ω)) pf (D₁ ω))
    foc {a Q .⁺ ⊃ B} pf (⊃I D₁) = ⊃R (L <> (foc (LIST.ALL.cons <> pf) D₁))
    foc {↓ A ⊃ B} pf (⊃I D₁) = ⊃R (L <> (foc (LIST.ALL.cons <> pf) D₁))
    foc {⊥ ⊃ B} pf (⊃I D₁) = ⊃R ⊥L
    foc {◇ A ⊃ B} pf (⊃I D₁) = u◇⊃I (foc (LIST.ALL.cons <> pf) D₁) 
    foc {□ A ⊃ B} pf (⊃I D₁) = u□⊃I (foc (LIST.ALL.cons <> pf) D₁)

    foc {A} pf (hyp x) = {!!}

    foc {A} pf (CORE.⊃E {B} D₁ D₂) = {!!}
    foc pf (⊥E ω D₁) with ω
    ... | ≺*≡ = u⊥E ω (foc pf D₁)
    ... | ≺*+ ω' = u⊥E ω (Pequiv.foc (ih _ ω') pf D₁) 
    foc pf (◇E ≺*≡ D₁ D₂) = {!!}
    foc pf (◇E (≺*+ y) D₁ D₂) = {!!}
    foc pf (□E ≺*≡ D₁ D₂) = {!!}
    foc pf (□E (≺*+ y) D₁ D₂) = {!!}
-}

{- with ω
    ... | ≺*≡  = 
      subst ω 
        (⊃E (hyp Z) (WK-N.wkN (⊆to/wken* ω (⊆to/refl _)) (defocV pf V₁)))
        (WK-N.wkN wkex (defocSp pf ω Sp₂))
    ... | ≺*+ ω' = {! subst ω ? (WK-N.wkN wkex (defocSp pf ω Sp₂))!} -}

   -- open SEQUENT UWF dec≺

{-

   -- Equivalence of natural deduction and sequent calculus
   -- Things are set up such that we have to prove both at once
   equivP : W → Set
   equivP = λ w → 
      ((∀{Γ A} → Γ ⊢ A [ w ] → Γ ⇒ A [ w ]) 
      × (∀{Γ A} → Γ ⇒ A [ w ] → Γ ⊢ A [ w ]))

   -- Given the induction hypothesis, natural deduction implies sequent
   

   nd→seq' : (w : W) → ((w' : W) → w ≺+ w' → equivP w') 
             → ∀{Γ A} → Γ ⊢ A [ w ] → Γ ⇒ A [ w ]
   nd→seq' w ih (hyp iN) = ident iN
   nd→seq' w ih (⊃I D) = ⊃R (nd→seq' w ih D)
   nd→seq' w ih (⊃E D D') = 
      cut (nd→seq' w ih D')
       (cut (wkS wken (nd→seq' w ih D))
        (⊃L ≺*≡ Z (ident (S Z)) (ident Z)))
   nd→seq' w ih (⊥E ≺*≡ D) = cut (nd→seq' w ih D) (⊥L ≺*≡ Z)
   nd→seq' w ih (⊥E (≺*+ ωh) D) = cut (fst (ih _ ωh) D) (⊥L (≺*+ ωh) Z)
   nd→seq' w ih (◇I ω D) = ◇R ω (fst (ih _ (≺+0 ω)) D)
   nd→seq' w ih (◇E ≺*≡ D D') = 
      cut (nd→seq' w ih D) 
       (◇L ≺*≡ Z λ ω D₀ → wkS wken 
        (nd→seq' w ih (D' ω (snd (ih _ (≺+0 ω)) (wkS (wkto ω) D₀)))))
   nd→seq' w ih (◇E (≺*+ ωh) D D') = 
      cut (fst (ih _ ωh) D) (◇L (≺*+ ωh) Z 
       λ ω D₀ → decut (fst (ih _ ωh) D) (nd→seq' w ih 
        (D' ω (snd (ih _ (≺+S' ωh ω)) (wkS (wkto ω) D₀)))))
   nd→seq' w ih (□I D) = □R (λ ω → fst (ih _ (≺+0 ω)) (D ω))
   nd→seq' w ih (□E ≺*≡ D D') =
      cut (nd→seq' w ih D) 
       (□L ≺*≡ Z (λ D₀ → wkS wken (nd→seq' w ih 
        (D' (λ ω → snd (ih _ (≺+0 ω)) (wkS (wkto ω) (D₀ ω)))))))
   nd→seq' w ih (□E (≺*+ ωh) D D') = 
     cut (fst (ih _ ωh) D) 
       (□L (≺*+ ωh) Z (λ D₀ → decut (fst (ih _ ωh) D) (nd→seq' w ih 
        (D' (λ ω → snd (ih _ (≺+S' ωh ω)) (wkS (wkto ω) (D₀ ω)))))))


   -- Therefore, both sequent calculus and natural deduction are equivalent
   nd⇆seq : (w : W) → 
      ((∀{Γ A} → Γ ⊢ A [ w ] → Γ ⇒ A [ w ]) 
      × (∀{Γ A} → Γ ⇒ A [ w ] → Γ ⊢ A [ w ]))
   nd⇆seq = 
      ind+ equivP (λ w ih → (λ D → nd→seq' _ ih D) , (λ D → seq→nd' _ ih D))

   nd→seq : ∀{Γ A w} → Γ ⊢ A [ w ] → Γ ⇒ A [ w ]
   nd→seq = fst (nd⇆seq _)

   seq→nd : ∀{Γ A w} → Γ ⇒ A [ w ] → Γ ⊢ A [ w ]
   seq→nd = snd (nd⇆seq _)

-}