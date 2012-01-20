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

  unpolx : ∀{Γ A w} 
    → (A at w) ∈ polΓ Γ 
    → (∃ λ B → ((B at w) ∈ Γ) × (polhyp (B at w) ≡ (A at w)))
  unpolx {[]} ()
  unpolx {(a Q ⁺ at w) :: Γ'} Z = (_ , Z , refl)
  unpolx {(⊥ at w) :: Γ'} Z = (_ , Z , refl)
  unpolx {(◇ A at w) :: Γ'} Z = (_ , Z , refl)
  unpolx {(□ A at w) :: Γ'} Z = (_ , Z , refl)
  unpolx {(a Q ⁻ at w) :: Γ'} Z = (_ , Z , refl)
  unpolx {((A ⊃ B) at w) :: Γ'} Z = (_ , Z , refl)
  unpolx {A :: Γ'} (S x) with unpolx {Γ'} x 
  ... | (_ , x' , refl) = (_ , S x' , refl)

  unpolx' : ∀{Γ A w} 
    → (↓ A at w) ∈ polΓ Γ 
    → (∃ λ B → ((B at w) ∈ Γ) × (pol⁻ B ≡ A))
  unpolx' {[]} ()
  unpolx' {(⊥ at w) :: Γ'} Z = (_ , Z , refl)
  unpolx' {(◇ A at w) :: Γ'} Z = (_ , Z , refl)
  unpolx' {(□ A at w) :: Γ'} Z = (_ , Z , refl)
  unpolx' {(a Q ⁻ at w) :: Γ'} Z = (_ , Z , refl)
  unpolx' {((A ⊃ B) at w) :: Γ'} Z = (_ , Z , refl)
  unpolx' {A :: Γ'} (S x) with unpolx' {Γ'} x 
  ... | (_ , x' , refl) = (_ , S x' , refl)


  Pfoc : W → Set
  Pfoc wc = ∀{A Γ}
    → Γ ⊢ A [ wc ]
    → Term [] (polΓ Γ) wc · (Reg (pol⁻ A))

  PdefocV : W → Set
  PdefocV wc = ∀{A Γ}
    → Value [] (polΓ Γ) wc (pol⁺ A)
    → Γ ⊢ A [ wc ]

  PdefocN : W → Set
  PdefocN wc = ∀{A Γ}
    → Term [] (polΓ Γ) wc · (Reg (pol⁻ A))
    → Γ ⊢ A [ wc ]

  PdefocSp : W → Set
  PdefocSp wc = ∀{B A Γ wh}
    → wc ≺* wh
    → Γ ⊢ B [ wh ]
    → Spine [] (polΓ Γ) wh (pol⁻ B) wc (Reg (pol⁻ A))
    → Γ ⊢ A [ wc ]

  Pfoc↑ : W → Set
  Pfoc↑ wc = ∀{A Γ}
    → Γ ⊢ A [ wc ]
    → Term [] (polΓ Γ) wc · (Reg (↑ (pol⁺ A)))

  Pdefoc↑ : W → Set
  Pdefoc↑ wc = ∀{A Γ}
    → Term [] (polΓ Γ) wc · (Reg (↑ (pol⁺ A)))
    → Γ ⊢ A [ wc ]
  

  record Pequiv (wc : W) : Set where
   field
    foc : Pfoc wc
    defocV : PdefocV wc
    defocN : PdefocN wc
    defocSp : PdefocSp wc
    foc↑ : Pfoc↑ wc
    defoc↑ : Pdefoc↑ wc

  module EQUIV-LEM (wc : W) (ih : (wc' : W) → wc ≺+ wc' → Pequiv wc') where

    defocV : PdefocV wc
    defocN : PdefocN wc
    defocSp : PdefocSp wc

    defocV {a Q ⁺} (pR x) with unpolx x
    defocV {a Q ⁺} (SEQUENT.pR x) | (a .Q ⁺ , x' , Refl) = hyp x'
    defocV {a Q ⁺} (SEQUENT.pR x) | (⊥ , x' , ())
    defocV {a Q ⁺} (SEQUENT.pR x) | (◇ A , x' , ())
    defocV {a Q ⁺} (SEQUENT.pR x) | (□ A , x' , ())
    defocV {a Q ⁺} (SEQUENT.pR x) | (a N ⁻ , x' , ())
    defocV {a Q ⁺} (SEQUENT.pR x) | (A ⊃ B , x' , ())
    defocV {⊥} ()
    defocV {◇ A} (◇R ω N₁) = ◇I ω (Pequiv.defoc↑ (ih _ (≺+0 ω)) N₁)
    defocV {□ A} (□R N₁) = □I λ ω → Pequiv.defoc↑ (ih _ (≺+0 ω)) (N₁ ω) 
    defocV {a Q ⁻} (↓R N₁) = defocN N₁
    defocV {A ⊃ B} (↓R N₁) = defocN N₁

    defocN {a Q ⁺} (↑R V₁) = defocV V₁
    defocN {⊥} (↑R V₁) = defocV V₁
    defocN {◇ A} (↑R V₁) = defocV V₁
    defocN {□ A} (↑R V₁) = defocV V₁
    defocN (↓L pf⁻ ωh x Sp) with unpolx' x
    ... | (_ , x' , Refl) = defocSp ωh (hyp x') Sp
    defocN {a Q ⁺ ⊃ B} (⊃R (L pf⁺ N₁)) = ⊃I (defocN N₁)
    defocN {a Q ⁻ ⊃ B} (⊃R (L pf⁺ N₁)) = ⊃I (defocN N₁)
    defocN {(A ⊃ B) ⊃ B'} (⊃R (L pf⁺ N₁)) = ⊃I (defocN N₁)
    defocN {⊥ ⊃ B} (⊃R ⊥L) = ⊃I (⊥E ≺*≡ (hyp Z))
    defocN {◇ A ⊃ B} (⊃R (◇L N₁)) = 
      ⊃I (◇E ≺*≡ (hyp Z)
           λ ω D₀ → 
             WK-N.wkN wken 
               (defocN (N₁ ω (wkN <> (⊆to/stenirrev (≺⊀ ω) (⊆to/refl _)) · 
                                (Pequiv.foc↑ (ih _ (≺+0 ω)) D₀)))))
    defocN {□ A ⊃ B} (⊃R (□L N₁)) = 
      ⊃I (□E ≺*≡ (hyp Z) 
           λ D₀ → 
             WK-N.wkN wken 
               (defocN (N₁ λ ω → wkN <> (⊆to/stenirrev (≺⊀ ω) (⊆to/refl _)) ·
                                   (Pequiv.foc↑ (ih _ (≺+0 ω)) (D₀ ω)))))
    defocN {⊥ ⊃ B} (⊃R (L () N₁))
    defocN {◇ A ⊃ B} (⊃R (L () N₁))
    defocN {□ A ⊃ B} (⊃R (L () N₁))

    defocSp {a N ⁺} ω D (↑L (L pf⁺ N₁)) = subst ω D (defocN N₁)
    defocSp {⊥} ω D (↑L ⊥L) = ⊥E ω D
    defocSp {◇ A} ω D (↑L (◇L N₁)) = 
      ◇E ω D λ ω' D₀ → defocN (N₁ ω' (Pequiv.foc↑ (ih _ (≺*S' ω ω')) D₀))
    defocSp {□ A} ω D (↑L (□L N₁)) = 
      □E ω D λ D₀ → defocN (N₁ λ ω' → Pequiv.foc↑ (ih _ (≺*S' ω ω')) (D₀ ω'))
    defocSp {a .Q ⁻} {a Q ⁻} ω D pL = D
    defocSp {a Q ⁻} {a N ⁺} ω D ()
    defocSp {a Q ⁻} {⊥} ω D ()
    defocSp {a Q ⁻} {A ⊃ B} ω D ()
    defocSp {a Q ⁻} {◇ A} ω D ()
    defocSp {a Q ⁻} {□ A} ω D ()
    defocSp {A ⊃ B} ω D (⊃L V₁ Sp₂) with ω
    ... | ≺*≡ = defocSp {B} ω (⊃E D (defocV V₁)) Sp₂
    ... | ≺*+ ω' = defocSp {B} ω (⊃E D (Pequiv.defocV (ih _ ω') V₁)) Sp₂
    defocSp {⊥} ω D (↑L (L () N₁))
    defocSp {◇ A} ω D (↑L (L () N₁))
    defocSp {□ A} ω D (↑L (L () N₁))    

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
               (↑L (◇L λ ω' N₀ →
                         ↑R (↓R (decut N₁ (N₂ ω' (cut N₁ N₀))))))))

    u□E : ∀{A w wc Γ C}
      → wc ≺* w
      → Term [] Γ w · (Reg (↑ (□ A)))
      → ((∀{w'} → w ≺ w' → Term [] Γ w' · (Reg (↑ A)))
          → Term [] Γ wc · (Reg C))
      → Term [] Γ wc · (Reg C)
    u□E ω N₁ N₂ = 
      u↓↑E (cut N₁ 
             (↓L <> ω Z 
               (↑L (□L λ N₀ → 
                         ↑R (↓R (decut N₁ (N₂ λ ω' → cut N₁ (N₀ ω'))))))))

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
    foc (◇E ωh D₁ D₂) = 
      u◇E ωh (foc* ωh D₁)
        λ ω N₀ → foc (D₂ ω (Pequiv.defoc↑ (ih _ (≺*S' ωh ω)) N₀))
    foc {□ (a N ⁺)} (CORE.□I D₁) = 
      ↑R (□R (λ ω → Pequiv.foc (ih _ (≺+0 ω)) (D₁ ω)))
    foc {□ ⊥} (CORE.□I D₁) = 
      ↑R (□R (λ ω → Pequiv.foc (ih _ (≺+0 ω)) (D₁ ω)))
    foc {□ (◇ A)} (CORE.□I D₁) = 
      ↑R (□R (λ ω → Pequiv.foc (ih _ (≺+0 ω)) (D₁ ω)))
    foc {□ (□ A)} (CORE.□I D₁) =
      ↑R (□R (λ ω → Pequiv.foc (ih _ (≺+0 ω)) (D₁ ω)))
    foc {□ (a N ⁻)} (CORE.□I D₁) = 
      ↑R (□R (λ ω → ↑R (↓R (Pequiv.foc (ih _ (≺+0 ω)) (D₁ ω)))))
    foc {□ (A ⊃ B)} (CORE.□I D₁) = 
      ↑R (□R (λ ω → ↑R (↓R (Pequiv.foc (ih _ (≺+0 ω)) (D₁ ω)))))
    foc (□E ωh D₁ D₂) = 
      u□E ωh (foc* ωh D₁) 
        λ N₀ → foc (D₂ λ ω → Pequiv.defoc↑ (ih _ (≺*S' ωh ω)) (N₀ ω))

    foc↑ : Pfoc↑ wc
    foc↑ {a Q ⁺} N = foc N
    foc↑ {⊥} N = foc N
    foc↑ {◇ A} N = foc N
    foc↑ {□ A} N = foc N
    foc↑ {a Q ⁻} N = ↑R (↓R (foc N))
    foc↑ {A ⊃ B} N = ↑R (↓R (foc N))

    defoc↑ : Pdefoc↑ wc
    defoc↑ {a Q ⁺} N = defocN N
    defoc↑ {⊥} N = defocN N
    defoc↑ {◇ A} N = defocN N
    defoc↑ {□ A} N = defocN N
    defoc↑ {a Q ⁻} N = defocN (u↓↑E N)
    defoc↑ {A ⊃ B} N = defocN (u↓↑E N)

  PFequiv : ∀{wc} → Pequiv wc
  PFequiv {wc} = ind+ Pequiv (λ wc ih → 
   record {
    foc = EQUIV-LEM.foc wc ih;
    defocV = EQUIV-LEM.defocV wc ih;
    defocN = EQUIV-LEM.defocN wc ih;
    defocSp = EQUIV-LEM.defocSp wc ih;
    foc↑ = EQUIV-LEM.foc↑ wc ih;
    defoc↑ = EQUIV-LEM.defoc↑ wc ih}) wc
 
  foc : ∀{wc} → Pfoc wc
  foc = Pequiv.foc PFequiv

  defocN : ∀{wc} → PdefocN wc
  defocN = Pequiv.defocN PFequiv