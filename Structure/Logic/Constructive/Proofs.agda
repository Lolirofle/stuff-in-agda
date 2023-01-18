module Structure.Logic.Constructive.Proofs where

open import Functional as Fn
open import Functional.Instance
open import Logic.Propositional as Logic using (_←_ ; _↔_)
open import Logic.Predicate     as Logic hiding (∀ₗ)
import      Lvl
import      Structure.Logic.Constructive.BoundedPredicate
import      Structure.Logic.Constructive.Predicate
import      Structure.Logic.Constructive.Propositional
open import Syntax.Function
open import Type

private variable ℓ ℓₗ ℓₘₗ ℓₒ ℓₚ : Lvl.Level
private variable Formula : Type{ℓₗ}
private variable Proof : Formula → Type{ℓₘₗ}
private variable Predicate : Type{ℓₚ}
private variable Domain : Type{ℓₒ}

module _ (Proof : Formula → Type{ℓₘₗ}) where
  open Structure.Logic.Constructive.Propositional(Proof)
  private variable X Y Z : Formula

  {-
  module _ ⦃ logic : ConstructiveLogic ⦄ where
    [⟵][⟶][∧]-[⟷]-equivalence : Proof(X ⟷ Y) ↔ (Proof(X ⟵ Y) Logic.∧ Proof(X ⟶ Y))
    [⟵][⟶][∧]-[⟷]-equivalence {X} {Y} = Logic.[↔]-intro
      (p ↦ ⟷.intro (⟵.elim(Logic.[∧]-elimₗ p)) (⟶.elim(Logic.[∧]-elimᵣ p)))
      (p ↦ Logic.[∧]-intro (⟵.intro (⟷.elimₗ p)) (⟶.intro (⟷.elimᵣ p)))
  -}

  [⟶]-redundancyₗ : ⦃ impl : ∃(Implication) ⦄ → Proof(X ⟶ (X ⟶ Y)) → Proof(X ⟶ Y)
  [⟶]-redundancyₗ = ⟶.intro ∘ swap apply₂ ∘ (⟶.elim ∘₂ ⟶.elim)

  [⟷]-reflexivity : ∀{_⟷_} → ⦃ Equivalence(_⟷_) ⦄ → Proof(X ⟷ X)
  [⟷]-reflexivity = ⟷.intro id id

  [⟵]-to-[⟶] : ⦃ con : ∃(Consequence) ⦄ → ∃(Implication)
  ∃.witness [⟵]-to-[⟶] = swap(_⟵_)
  Implication.intro (∃.proof [⟵]-to-[⟶]) = ⟵.intro
  Implication.elim  (∃.proof [⟵]-to-[⟶]) = ⟵.elim

  [⟶]-to-[⟵] : ⦃ impl : ∃(Implication) ⦄ → ∃(Consequence)
  ∃.witness [⟶]-to-[⟵] = swap(_⟶_)
  Consequence.intro (∃.proof [⟶]-to-[⟵]) = ⟶.intro
  Consequence.elim  (∃.proof [⟶]-to-[⟵]) = ⟶.elim

  [⟵][⟶][∧]-to-[⟷] : ⦃ con : ∃(Consequence) ⦄ → ⦃ impl : ∃(Implication) ⦄ → ⦃ or : ∃(Conjunction) ⦄ → ∃(Equivalence)
  ∃.witness [⟵][⟶][∧]-to-[⟷] X Y = (X ⟵ Y) ∧ (X ⟶ Y)
  Equivalence.intro (∃.proof [⟵][⟶][∧]-to-[⟷]) yx xy = ∧.intro (⟵.intro yx) (⟶.intro xy)
  Equivalence.elimₗ (∃.proof [⟵][⟶][∧]-to-[⟷])       = ⟵.elim ∘ ∧.elimₗ
  Equivalence.elimᵣ (∃.proof [⟵][⟶][∧]-to-[⟷])       = ⟶.elim ∘ ∧.elimᵣ

  [⟶][⟷]-to-[∧] : ⦃ impl : ∃(Implication) ⦄ → ⦃ eq : ∃(Equivalence) ⦄ → ∃(Conjunction)
  ∃.witness [⟶][⟷]-to-[∧] X Y = (X ⟶ Y) ⟷ X
  Conjunction.intro (∃.proof [⟶][⟷]-to-[∧]) x y = ⟷.intro (const(⟶.intro(const y))) (const x)
  Conjunction.elimₗ (∃.proof [⟶][⟷]-to-[∧]) xyx = ⟷.elimᵣ xyx (⟶.intro(swap apply₂(⟶.elim ∘ ⟷.elimₗ xyx)))
  Conjunction.elimᵣ (∃.proof [⟶][⟷]-to-[∧]) xyx = apply₂(⟷.elimᵣ xyx (⟶.intro(swap apply₂ (⟶.elim ∘ ⟷.elimₗ xyx)))) (⟶.elim ∘ (⟷.elimₗ xyx))

  [∨][⟷]-to-[⟶] : ⦃ or : ∃(Disjunction) ⦄ → ⦃ eq : ∃(Equivalence) ⦄ → ∃(Implication)
  ∃.witness [∨][⟷]-to-[⟶] X Y = (X ∨ Y) ⟷ Y
  Implication.intro (∃.proof [∨][⟷]-to-[⟶])       = ⟷.intro ∨.introᵣ ∘ swap ∨.elim id
  Implication.elim  (∃.proof [∨][⟷]-to-[⟶]) xyy x = ⟷.elimᵣ xyy (∨.introₗ x)

  [∧][⟷]-to-[⟶] : ⦃ and : ∃(Conjunction) ⦄ → ⦃ eq : ∃(Equivalence) ⦄ → ∃(Implication)
  ∃.witness [∧][⟷]-to-[⟶] X Y = (X ∧ Y) ⟷ X
  Implication.intro (∃.proof [∧][⟷]-to-[⟶]) xy    = ⟷.intro (x ↦ ∧.intro x (xy x)) ∧.elimₗ
  Implication.elim  (∃.proof [∧][⟷]-to-[⟶]) xyx x = ∧.elimᵣ(⟷.elimₗ xyx x)

  [¬][⊤]-to-[⊥] : ⦃ neg : ∃(Negation) ⦄ → ⦃ top : ∃(Top) ⦄ → ∃(Bottom)
  ∃.witness [¬][⊤]-to-[⊥] = ¬ ⊤
  Bottom.elim (∃.proof [¬][⊤]-to-[⊥]) = ¬.elim ⊤.intro

  [¬][⊥]-to-[⊤] : ⦃ neg : ∃(Negation) ⦄ → ⦃ bot : ∃(Bottom) ⦄ → ∃(Top)
  ∃.witness [¬][⊥]-to-[⊤] = ¬ ⊥
  Top.intro (∃.proof [¬][⊥]-to-[⊤]) = ¬.intro{Y = ⊥} ⊥.elim ⊥.elim

  {- TODO: Move these to Classical
  [¬][∨]-to-[∧] : ⦃ neg : ∃(Negation) ⦄ → ⦃ or : ∃(Disjunction) ⦄ → ∃(Conjunction)
  ∃.witness [¬][∨]-to-[∧] X Y = ¬((¬ X) ∨ (¬ Y))
  Conjunction.intro (∃.proof [¬][∨]-to-[∧]) {X} x y = ¬.intro{Y = X} (∨.elim (¬.elim x) (¬.elim y)) (∨.elim (¬.elim x) (¬.elim y))
  Conjunction.elimₗ (∃.proof [¬][∨]-to-[∧]) nnxny = ¬.elim (∨.introₗ (¬.intro {!!} {!!})) nnxny
  Conjunction.elimᵣ (∃.proof [¬][∨]-to-[∧]) nnxny = {!!}

  [¬][∧]-to-[∨] : ⦃ neg : ∃(Negation) ⦄ → ⦃ and : ∃(Conjunction) ⦄ → ∃(Disjunction)
  ∃.witness [¬][∧]-to-[∨] X Y = ¬((¬ X) ∧ (¬ Y))
  Disjunction.introₗ (∃.proof [¬][∧]-to-[∨]) {X} x = ¬.intro {Y = X} (¬.elim x ∘ ∧.elimₗ) (¬.elim x ∘ ∧.elimₗ)
  Disjunction.introᵣ (∃.proof [¬][∧]-to-[∨]) {X} y = ¬.intro {Y = X} (¬.elim y ∘ ∧.elimᵣ) (¬.elim y ∘ ∧.elimᵣ)
  Disjunction.elim   (∃.proof [¬][∧]-to-[∨]) xz yz nnxny = {!!}
  -- ¬.elim {!!} nnxny
  -}

  [⟷]-to-[⊤] : Formula → ⦃ eq : ∃(Equivalence) ⦄ → ∃(Top)
  ∃.witness ([⟷]-to-[⊤] φ) = φ ⟷ φ
  Top.intro (∃.proof ([⟷]-to-[⊤] φ)) = [⟷]-reflexivity

  [⟷][⊥]-to-[¬] : ⦃ eq : ∃(Equivalence) ⦄ → ⦃ bot : ∃(Bottom) ⦄ → ∃(Negation)
  ∃.witness [⟷][⊥]-to-[¬] = _⟷ ⊥
  Negation.intro (∃.proof [⟷][⊥]-to-[¬]) xy xy⊥ = ⟷.intro ⊥.elim ((⟷.elimᵣ ∘ xy⊥) ∘ₛ xy)
  Negation.elim  (∃.proof [⟷][⊥]-to-[¬])        = ⊥.elim ∘₂ swap ⟷.elimᵣ

  [⟶][⊥]-to-[¬] : ⦃ eq : ∃(Implication) ⦄ → ⦃ bot : ∃(Bottom) ⦄ → ∃(Negation)
  ∃.witness [⟶][⊥]-to-[¬] = _⟶ ⊥
  Negation.intro (∃.proof [⟶][⊥]-to-[¬]) xy xy⊥ = ⟶.intro ((swap ⟶.elim ∘ xy) ∘ₛ xy⊥)
  Negation.elim  (∃.proof [⟶][⊥]-to-[¬])        = ⊥.elim ∘₂ swap ⟶.elim

  [∨][⟷][⊥]-adequacy : ⦃ or : ∃(Disjunction) ⦄ → ⦃ eq : ∃(Equivalence) ⦄ → ⦃ bot : ∃(Bottom) ⦄ → Logic
  Logic.top         [∨][⟷][⊥]-adequacy = [⟷]-to-[⊤] ⊥
  Logic.implication [∨][⟷][⊥]-adequacy = [∨][⟷]-to-[⟶]
  Logic.negation    [∨][⟷][⊥]-adequacy = [⟷][⊥]-to-[¬]
  Logic.conjunction [∨][⟷][⊥]-adequacy = [⟶][⟷]-to-[∧] where instance _ = Logic.implication [∨][⟷][⊥]-adequacy
  Logic.consequence [∨][⟷][⊥]-adequacy = [⟶]-to-[⟵]    where instance _ = Logic.implication [∨][⟷][⊥]-adequacy

  [⟶][∧][∨][⊤][⊥]-adequacy : ⦃ impl : ∃(Implication) ⦄ → ⦃ and : ∃(Conjunction) ⦄ → ⦃ or : ∃(Disjunction) ⦄ → ⦃ top : ∃(Top) ⦄ → ⦃ bot : ∃(Bottom) ⦄ → Logic
  Logic.consequence [⟶][∧][∨][⊤][⊥]-adequacy = [⟶]-to-[⟵]
  Logic.equivalence [⟶][∧][∨][⊤][⊥]-adequacy = [⟵][⟶][∧]-to-[⟷] where instance _ = Logic.consequence [⟶][∧][∨][⊤][⊥]-adequacy
  Logic.negation    [⟶][∧][∨][⊤][⊥]-adequacy = [⟶][⊥]-to-[¬]

module _ (Proof : Formula → Type{ℓₘₗ}) where
  open Structure.Logic.Constructive.Propositional(Proof)
  private variable X Y Z : Formula

  open import Data.Tuple as Tuple using ()

  [⊤]-preserving-type : ⦃ top : ∃(Top) ⦄ → Proof(⊤) ↔ Logic.⊤
  Tuple.left  [⊤]-preserving-type = const ⊤.intro
  Tuple.right [⊤]-preserving-type = const Logic.[⊤]-intro

  [∧]-preserving-type : ⦃ and : ∃(Conjunction) ⦄ → Proof(X ∧ Y) ↔ (Proof(X) Logic.∧ Proof(Y))
  Tuple.left  [∧]-preserving-type (Logic.[∧]-intro x y) = ∧.intro x y
  Tuple.right [∧]-preserving-type xy                    = Logic.[∧]-intro (∧.elimₗ xy) (∧.elimᵣ xy)

  [∨]-preserving-type : ⦃ or : ∃(Disjunction) ⦄ → Proof(X ∨ Y) ← (Proof(X) Logic.∨ Proof(Y))
  [∨]-preserving-type = Logic.[∨]-elim ∨.introₗ ∨.introᵣ

  [⟶]-preserving-type : ⦃ impl : ∃(Implication) ⦄ → Proof(X ⟶ Y) ↔ (Proof(X) → Proof(Y))
  Tuple.left  [⟶]-preserving-type = ⟶.intro
  Tuple.right [⟶]-preserving-type = ⟶.elim

  [⟵]-preserving-type : ⦃ cons : ∃(Consequence) ⦄ → Proof(X ⟵ Y) ↔ (Proof(X) ← Proof(Y))
  Tuple.left  [⟵]-preserving-type = ⟵.intro
  Tuple.right [⟵]-preserving-type = ⟵.elim

  [⟷]-preserving-type : ⦃ eq : ∃(Equivalence) ⦄ → Proof(X ⟷ Y) ↔ (Proof(X) ↔ Proof(Y))
  Tuple.left  [⟷]-preserving-type xy = ⟷.intro (Logic.[↔]-to-[←] xy) (Logic.[↔]-to-[→] xy)
  Tuple.right [⟷]-preserving-type xy = Logic.[↔]-intro (⟷.elimₗ xy) (⟷.elimᵣ xy)

  {-
  module Test ⦃ logic : Logic ⦄ where
    pure : ∀{A : Formula} → Proof(A) → Proof(A)
    pure = id

    _<*>_ : ∀{A B : Formula} → Proof(A ⟶ B) → Proof(A) → Proof(B)
    _<*>_ = ⟶.elim

    test : ∀{A B} → Proof(A ⟶ (A ⟶ B)) → Proof(A) → Proof(B)
    test ab a = ⦇ ab a a ⦈

  module Test2 ⦃ logic : ConstructiveLogic ⦄ {Obj : Type{ℓ}} where
    private variable P : Obj → Formula

    module _ ⦃ all : ∃(Universal) ⦄ where
      pure : ∀{A : Formula} → Proof(A) → Proof(A)
      pure = id

      _<*>_ : ∀{P : Obj → Formula} → Proof(∀ₗ P) → (x : Obj) → Proof(P(x))
      _<*>_ = ∀ₗ.elim

      test : ∀{A : Obj → Obj → Formula} → Proof(∀ₗ(x ↦ ∀ₗ(y ↦ A x y))) → (x : Obj) → Proof(A x x)
      test a x  = ⦇ a x x ⦈
  -}

module _ where
  open import Data
  open import Data.Tuple
  open import Data.Either as Either
  open        Structure.Logic.Constructive.BoundedPredicate renaming (Logic to BoundedPredicateLogic)
  open        Structure.Logic.Constructive.Predicate        renaming (Logic to PredicateLogic)
  open        Structure.Logic.Constructive.Propositional    renaming (Logic to PropositionalLogic)

  instance
    typePropositionalLogic : PropositionalLogic{Formula = Type{ℓ}} id
    PropositionalLogic.bottom      typePropositionalLogic = [∃]-intro Empty     ⦃ record{elim = empty} ⦄
    PropositionalLogic.top         typePropositionalLogic = [∃]-intro Unit      ⦃ record{intro = <>} ⦄
    PropositionalLogic.implication typePropositionalLogic = [∃]-intro _→ᶠ_      ⦃ record{intro = _$_ ; elim = id} ⦄
    PropositionalLogic.conjunction typePropositionalLogic = [∃]-intro _⨯_       ⦃ record{intro = _,_ ; elimₗ = left ; elimᵣ = right} ⦄
    PropositionalLogic.disjunction typePropositionalLogic = [∃]-intro _‖_       ⦃ record{introₗ = Left ; introᵣ = Right ; elim = Either.map1} ⦄
    PropositionalLogic.consequence typePropositionalLogic = [∃]-intro _←ᶠ_      ⦃ record{intro = id ; elim = _$_} ⦄
    PropositionalLogic.equivalence typePropositionalLogic = [∃]-intro Logic._↔_ ⦃ record{intro = _,_ ; elimₗ = left ; elimᵣ = right} ⦄
    PropositionalLogic.negation    typePropositionalLogic = [∃]-intro Logic.¬_  ⦃ record{intro = Fn.swap(_∘ₛ_) ; elim = empty ∘₂ apply} ⦄

  instance
    typePredicateLogic : ∀{T : Type{ℓₒ}} → PredicateLogic{Formula = Type{ℓₒ Lvl.⊔ ℓₗ}} id {Predicate = T → Type{ℓₒ Lvl.⊔ ℓₗ}} {Domain = T} id
    PredicateLogic.universal   typePredicateLogic = [∃]-intro Logic.∀ₗ ⦃ record{intro = id ; elim = id} ⦄
    PredicateLogic.existential typePredicateLogic = [∃]-intro Logic.∃  ⦃ record{intro = \{_}{x} p → Logic.[∃]-intro x ⦃ p ⦄ ; elim = Logic.[∃]-elim} ⦄

  open import Type.Dependent.Sigma
  
  instance
    typeBoundedPredicateLogic : ∀{T : Type{ℓₒ}} → BoundedPredicateLogic{Formula = Type{ℓₒ Lvl.⊔ ℓₗ}} id {Predicate = (x : T) → ∀{B : T → Type{ℓₒ Lvl.⊔ ℓₗ}} → B(x) → Type{ℓₒ Lvl.⊔ ℓₗ}} {Domain = T} id
    BoundedPredicateLogic.universal   typeBoundedPredicateLogic = [∃]-intro (\B P → ∀{x} → (bx : B(x)) → P(x){B}(bx)) ⦃ record{intro = \p bx → p bx ; elim = \p bx → p bx} ⦄
    BoundedPredicateLogic.existential typeBoundedPredicateLogic = [∃]-intro (\B P → Logic.∃(x ↦ Σ(B(x)) (P(x){B}))) ⦃ record{intro = \{_}{x} bx p → Logic.[∃]-intro x ⦃ intro bx p ⦄ ; elim = \p → Logic.[∃]-elim (\(intro bx px) → p bx px)} ⦄

  {- TODO: Maybe have some more assumptions
  boundedPredicateLogic-to-predicateLogic : ∀{Formula Domain Predicate : Type{ℓₒ}}{Proof : Formula → Type}{_$_} → BoundedPredicateLogic{Formula = Formula} Proof {Predicate = Predicate} {Domain = Domain} (_$_) → PredicateLogic{Formula = Formula} Proof {Predicate = (Domain → Formula) ⨯ Predicate} {Domain = Σ(Predicate ⨯ Domain) (\(P , x) → Proof((P $ x) {{!!}} {!!}))} {!!}
  PredicateLogic.propositional (boundedPredicateLogic-to-predicateLogic L) = BoundedPredicateLogic.propositional L
  ∃.witness (PredicateLogic.universal (boundedPredicateLogic-to-predicateLogic L)) (B , P) = ∃.witness (BoundedPredicateLogic.universal L) B P
  Universal.intro (∃.proof (PredicateLogic.universal (boundedPredicateLogic-to-predicateLogic L))) {B , P} p = BoundedUniversal.intro
                                                                                                         (∃.proof (BoundedPredicateLogic.universal L)) (\{x} pp → p{intro (P , x) {!!}})
  Universal.elim (∃.proof (PredicateLogic.universal (boundedPredicateLogic-to-predicateLogic L))) = {!!}
  ∃.witness (PredicateLogic.existential (boundedPredicateLogic-to-predicateLogic L)) (B , P) = ∃.witness (BoundedPredicateLogic.existential L) B P
  Existential.intro (∃.proof (PredicateLogic.existential (boundedPredicateLogic-to-predicateLogic L))) = {!!}
  Existential.elim (∃.proof (PredicateLogic.existential (boundedPredicateLogic-to-predicateLogic L))) = {!!}
  -}

  {- TODO: Seems to need a duplicate (Domain → Formula) in Predicate. Also, does not work with this generality
  boundedPredicateLogic-to-predicateLogic : ∀{_$_} → BoundedPredicateLogic{Formula = Formula} Proof {Predicate = Predicate} {Domain = Domain} (_$_) → PredicateLogic{Formula = Formula} Proof {Predicate = Predicate} {Domain = Σ((Domain → Formula) ⨯ Domain) (\(B , x) → Proof(B(x)))} (\P (intro(B , x) bx) → (P $ x) {B} bx)
  PredicateLogic.propositional (boundedPredicateLogic-to-predicateLogic L) = BoundedPredicateLogic.propositional L
  PredicateLogic.universal (boundedPredicateLogic-to-predicateLogic L) = [∃]-intro {!!} ⦃ record{intro = {!!} ; elim = {!!}} ⦄
  PredicateLogic.existential (boundedPredicateLogic-to-predicateLogic L) = [∃]-intro {!!} ⦃ record{intro = {!!} ; elim = {!!}} ⦄
  -}

  {-instance
    typeBoundedPredicateLogic : ∀{T : Type{ℓₒ}}{B : T → Type{ℓ}} → PredicateLogic{Formula = Type{ℓₒ Lvl.⊔ ℓₗ Lvl.⊔ ℓ}} id {Predicate = (x : T) → ⦃ B(x) ⦄ → Type{ℓₒ Lvl.⊔ ℓₗ Lvl.⊔ ℓ}} {Domain = Σ T B} (\f (intro x b) → f x ⦃ b ⦄)
    PredicateLogic.universal   (typeBoundedPredicateLogic {B = B}) = [∃]-intro (f ↦ (∀{x} ⦃ bx ⦄ → f(x) ⦃ bx ⦄)) ⦃ record{intro = \px → px ; elim = \{P} px {x} → px{Σ.left x} ⦃ Σ.right x ⦄} ⦄
    PredicateLogic.existential (typeBoundedPredicateLogic {B = B}) = [∃]-intro (f ↦ Logic.∃(x ↦ Σ(B(x)) (bx ↦ f x ⦃ bx ⦄)) ) ⦃ record{intro = {!!} ; elim = {!!}} ⦄
  -}

  import      Logic.Classical.DoubleNegated as DoubleNegated
  open import Logic.Names
  import      Logic.Propositional.Theorems as Logic
  instance
    doubleNegatedTypeLogic : PropositionalLogic{ℓₘₗ = Lvl.𝟎}(Logic.¬¬_)
    PropositionalLogic.bottom      doubleNegatedTypeLogic = Logic.[∃]-intro Logic.⊥     ⦃ record{elim = DoubleNegated.[⊥]-elim} ⦄
    PropositionalLogic.top         doubleNegatedTypeLogic = Logic.[∃]-intro Logic.⊤     ⦃ record{intro = DoubleNegated.[⊤]-intro} ⦄
    PropositionalLogic.implication doubleNegatedTypeLogic = Logic.[∃]-intro (_→ᶠ_)      ⦃ record{intro = DoubleNegated.[→]-intro ; elim = DoubleNegated.[→]-elim} ⦄
    PropositionalLogic.conjunction doubleNegatedTypeLogic = Logic.[∃]-intro (Logic._∧_) ⦃ record{intro = DoubleNegated.[∧]-intro ; elimₗ = DoubleNegated.[∧]-elimₗ ; elimᵣ = DoubleNegated.[∧]-elimᵣ} ⦄
    PropositionalLogic.disjunction doubleNegatedTypeLogic = Logic.[∃]-intro (Logic._∨_) ⦃ record{introₗ = DoubleNegated.[∨]-introₗ ; introᵣ = DoubleNegated.[∨]-introᵣ ; elim = DoubleNegated.[∨]-elim} ⦄
    PropositionalLogic.consequence doubleNegatedTypeLogic = Logic.[∃]-intro (Logic._←_) ⦃ record{intro = DoubleNegated.[←]-intro ; elim = DoubleNegated.[→]-elim} ⦄
    PropositionalLogic.equivalence doubleNegatedTypeLogic = Logic.[∃]-intro (Logic._↔_) ⦃ record{intro = DoubleNegated.[↔]-intro ; elimₗ = DoubleNegated.[↔]-elimₗ ; elimᵣ = DoubleNegated.[↔]-elimᵣ} ⦄
    PropositionalLogic.negation    doubleNegatedTypeLogic = Logic.[∃]-intro (Logic.¬_)  ⦃ record{intro = Fn.swap(_∘ₛ_) ; elim = const ∘₂ apply} ⦄

  open import Data.Boolean
  import      Data.Boolean.Operators
  open        Data.Boolean.Operators.Programming
  open import Data.Boolean.Stmt
  open import Data.Boolean.Stmt.Logic
  instance
    booleanLogic : PropositionalLogic IsTrue
    PropositionalLogic.bottom      booleanLogic = [∃]-intro 𝐹    ⦃ record{elim = Logic.[⊥]-elim ∘ IsTrue.[𝐹]-elim} ⦄
    PropositionalLogic.top         booleanLogic = [∃]-intro 𝑇    ⦃ record{intro = IsTrue.[𝑇]-intro} ⦄
    PropositionalLogic.conjunction booleanLogic = [∃]-intro _&&_ ⦃ record{intro = IsTrue.[∧]-intro ; elimₗ = IsTrue.[∧]-elimₗ ; elimᵣ = IsTrue.[∧]-elimᵣ} ⦄
    PropositionalLogic.disjunction booleanLogic = [∃]-intro _||_ ⦃ record{introₗ = IsTrue.[∨]-introₗ ; introᵣ = IsTrue.[∨]-introᵣ ; elim = IsTrue.[∨]-elim} ⦄
    PropositionalLogic.negation    booleanLogic = [∃]-intro !    ⦃ record{intro = IsTrue.[!]-intro ; elim = IsTrue.[!]-elim} ⦄
    PropositionalLogic.implication booleanLogic = [∃]-intro _→?_ ⦃ record{intro = IsTrue.[→?]-intro ; elim = IsTrue.[→?]-elim} ⦄
    PropositionalLogic.consequence booleanLogic = [∃]-intro _←?_ ⦃ record{intro = IsTrue.[←?]-intro ; elim = IsTrue.[←?]-elim} ⦄
    PropositionalLogic.equivalence booleanLogic = [∃]-intro _==_ ⦃ record{intro = IsTrue.[==]-intro ; elimₗ = IsTrue.[==]-elimₗ ; elimᵣ = IsTrue.[==]-elimᵣ} ⦄

  booleanPredicateLogic : ∀{T : Type{ℓ}}{all exist : (T → Bool) → Bool} → (∀{P} → (∀{x} → IsTrue(P(x))) ↔ IsTrue(all P)) → (∀{P} → (Logic.∃(x ↦ IsTrue(P(x)))) ↔ IsTrue(exist P)) → PredicateLogic IsTrue {Domain = T} id
  PredicateLogic.universal   (booleanPredicateLogic {all = all} {exist = exist} all-eq exist-eq) = [∃]-intro all   ⦃ record{intro = Logic.[↔]-to-[→] all-eq ; elim = Logic.[↔]-to-[←] all-eq} ⦄
  PredicateLogic.existential (booleanPredicateLogic {all = all} {exist = exist} all-eq exist-eq) = [∃]-intro exist ⦃ record{intro = Logic.[↔]-to-[→] exist-eq ∘ (p ↦ [∃]-intro _ ⦃ p ⦄) ; elim = p ↦ ep ↦ p(Logic.[∃]-proof(Logic.[↔]-to-[←] exist-eq ep))} ⦄
