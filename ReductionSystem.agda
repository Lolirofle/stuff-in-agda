open import Type

-- The relation (_⟶_) should be interpreted as "a term reduces/rewritten to another term".
-- Also called: Abstract reduction system, abstract rewriting system, rewriting system.
module ReductionSystem {ℓ₁ ℓ₂} {Term : Type{ℓ₁}} (_⟶_ : Term → Term → Type{ℓ₂}) where

open import Functional
open import Graph.Properties
open import Graph.Walk
open import Graph.Walk.Proofs
open import Functional.Instance
import      Lvl
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Relator.Converse
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Relator.ReflexiveTransitiveClosure
open import Structure.Setoid.Uniqueness
open import Structure.Relator.Equivalence
open import Structure.Relator.Ordering
open import Structure.Relator.Properties
open import Syntax.Function
open import Syntax.Transitivity

open Graph.Properties using (intro) public

-- The relation (_⟶_) is a function on the left argument.
-- In terms of paths, it means that there are no forks on any paths.
Deterministic = ∀{a} → Unique(a ⟶_)

-- A term is reducible when there is a term it can reduce to.
-- In terms of paths, it means that one can go somewhere else from this point.
Reducible : Term → Stmt
Reducible(a) = ∃(a ⟶_)

-- A term is in normal form when it is irreducible (cannot be reduced any further).
-- Also called: Irreducible term
-- In terms of paths, it means that this point is a dead-end.
NormalForm : Term → Stmt
NormalForm = FinalVertex(_⟶_)
module NormalForm = FinalVertex

-- "a normalizes to b" means that "a" reduces to the normal form "b".
-- In terms of paths, this means that the dead end of one path from "a" is "b".
record _normalizes-to_ (a : Term) (b : Term) : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
  constructor intro
  field
    reduction : Walk(_⟶_) a b
    ⦃ normalForm ⦄ : NormalForm(b)

-- In terms of paths, this means that there is a path which leads to a dead-end.
WeaklyNormalizes : Term → Stmt
WeaklyNormalizes a = ∃(a normalizes-to_)

-- A reduction system is weakly normalizing when all terms in the language have a normal form.
-- In terms of paths, this means that all points have a path whch eventually lead to a dead-end.
WeaklyNormalizing = ∀ₗ(WeaklyNormalizes)

StronglyNormalizes : Term → Stmt
StronglyNormalizes = Strict.Properties.Accessibleₗ(Converse(_⟶_))

-- Every term reduces to a normal form.
-- Also called: Terminating.
StronglyNormalizing : Stmt
StronglyNormalizing = Strict.Properties.WellFounded(Converse(_⟶_))

-- Both a and b reduce to c in zero or more steps.
-- Also called: _⟶*_*⟵_
CommonReduct : Term → Term → Term → Stmt
CommonReduct c a b = (Walk(_⟶_) a c) ∧ (Walk(_⟶_) b c)

-- Both a and b reduce to the same term in zero or more steps.
-- In terms of paths, this means that paths starting from the two points are able to eventually meet.
-- Also called: Joinable, _⟶*_*⟵_ _↓_.
Joinable : Term → Term → Stmt
Joinable a b = ∃(c ↦ CommonReduct c a b)

module Names where
  import Structure.Relator.Names as Names

  EverywhereCommonReduct = Names.Subrelation (Walk(_⟶_)) Joinable

  module _ (a : Term) where
    Confluent         = ∀{b c} → (Walk(_⟶_) a b) → (Walk(_⟶_) a c) → Joinable b c
    Semiconfluent     = ∀{b c} → (a ⟶ b)         → (Walk(_⟶_) a c) → Joinable b c
    LocallyConfluent  = ∀{b c} → (a ⟶ b)         → (a ⟶ c)         → Joinable b c
    StronglyConfluent = ∀{b c} → (a ⟶ b)         → (a ⟶ c)         → ∃(d ↦ (ReflexiveClosure(_⟶_) b d) ∧ (Walk(_⟶_) c d))
    DiamondProperty   = ∀{b c} → (a ⟶ b)         → (a ⟶ c)         → ∃(d ↦ (b ⟶ d) ∧ (c ⟶ d))

  Confluence = ∀ₗ(Confluent)

-- Also called: The Church-Rosser property
EverywhereCommonReduct = (Walk(_⟶_)) ⊆₂ Joinable

module _ (a : Term) where
  -- A term is confluent when all its reducts have a common reduct.
  -- In terms of paths, this means that paths starting from this point will always eventually meet.
  record Confluent : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : Names.Confluent(a)
  confluent = inferArg Confluent.proof

  record Semiconfluent : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : Names.Semiconfluent(a)
  semiconfluent = inferArg Semiconfluent.proof

  record LocallyConfluent : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : Names.LocallyConfluent(a)
  locally-confluent = inferArg LocallyConfluent.proof

  record StronglyConfluent : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : Names.StronglyConfluent(a)
  strongly-confluent = inferArg StronglyConfluent.proof

  record DiamondProperty : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : Names.DiamondProperty(a)
  diamond-property = inferArg DiamondProperty.proof

-- All terms are confluent.
-- In terms of paths, this means that parts starting from the same point can always eventually meet.
Confluence = ∀ₗ(Confluent)

Semiconfluence = ∀ₗ(Semiconfluent)

LocalConfluence = ∀ₗ(LocallyConfluent)

StrongConfluence = ∀ₗ(StronglyConfluent)

record Convergent : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
  constructor intro
  field
    ⦃ confluence ⦄ : Confluence
    ⦃ strongly-normalizing ⦄ : StronglyNormalizing

-- Evaluable = ∃(f ↦ )



-- All paths from a dead-end results in going nowhere.
Normal-unique-Path : ∀{a} → ⦃ _ : NormalForm(a) ⦄ → ∀{b} → Walk(_⟶_) a b → (a ≡ b)
Normal-unique-Path              at                 = [≡]-intro
Normal-unique-Path ⦃ intro na ⦄ (prepend ab1 sb1b) = [⊥]-elim(na ab1)

instance
  -- A term reduces to itself in zero steps.
  -- In terms of paths, this means that two paths starting from the same point can reach this same point.
  Joinable-reflexivity : Reflexivity(Joinable)
  ∃.witness (Reflexivity.proof Joinable-reflexivity {x}) = x
  ∃.proof   (Reflexivity.proof Joinable-reflexivity {x}) = [∧]-intro Walk.at Walk.at

instance
  -- When one reduces to the same term as the other, the other also reduces to the same term as the first one.
  Joinable-symmetry : Symmetry(Joinable)
  ∃.witness (Symmetry.proof Joinable-symmetry {x} {y} xy) = [∃]-witness xy
  ∃.proof   (Symmetry.proof Joinable-symmetry {x} {y} xy) = [∧]-intro ([∧]-elimᵣ(∃.proof xy)) (([∧]-elimₗ(∃.proof xy)))

instance
  -- When one reduces to the same term as the other, the other also reduces to the same term as the first one.
  Walk-Joinable-subrelation : Walk(_⟶_) ⊆₂ Joinable
  ∃.witness (_⊆₂_.proof Walk-Joinable-subrelation {y = y} ab) = y
  ∃.proof   (_⊆₂_.proof Walk-Joinable-subrelation ab) = [∧]-intro ab (reflexivity(Walk(_⟶_)))

module _ ⦃ confl : Confluence ⦄ where
  import      Structure.Relator.Names as Names

  instance
    Confluence-to-Joinable-transitivity : Transitivity(Joinable)
    Confluence-to-Joinable-transitivity = intro proof where
      proof : Names.Transitivity(Joinable)
      proof {x}{y}{z} ([∃]-intro obj-xy ⦃ [∧]-intro pxxy pyxy ⦄) ([∃]-intro obj-yz ⦃ [∧]-intro pyyz pzyz ⦄) = [∃]-intro obj ⦃ [∧]-intro l r ⦄ where
        objxy-objyz-common-reduct : Joinable obj-xy obj-yz
        objxy-objyz-common-reduct = confluent(y) pyxy pyyz

        obj : Term
        obj = [∃]-witness objxy-objyz-common-reduct

        l : Walk(_⟶_) x obj
        l = transitivity(Walk(_⟶_)) pxxy ([∧]-elimₗ ([∃]-proof objxy-objyz-common-reduct))

        r : Walk(_⟶_) z obj
        r = transitivity(Walk(_⟶_)) pzyz ([∧]-elimᵣ ([∃]-proof objxy-objyz-common-reduct))

  instance
    Confluence-to-Joinable-equivalence : Equivalence(Joinable)
    Confluence-to-Joinable-equivalence = intro

module _ (det : Deterministic) where
  -- Frege thing
  deterministic-dichotomy : ∀{a b c} → (Walk(_⟶_) a b) → (Walk(_⟶_) a c) → (Walk(_⟶_) b c) ∨ (Walk(_⟶_) c b)
  deterministic-dichotomy at ac = [∨]-introₗ ac
  deterministic-dichotomy (ab @ (prepend _ _)) at = [∨]-introᵣ ab
  deterministic-dichotomy (prepend ab2 b) (prepend ab3 ac) with det ab2 ab3
  ... | [≡]-intro = deterministic-dichotomy b ac

  deterministic-step : ∀{a b c} → (a ⟶ b) → (Walk(_⟶_) a c) → ((a ≡ c) ∨ (Walk(_⟶_) b c))
  deterministic-step ab at = [∨]-introₗ [≡]-intro
  deterministic-step ab (prepend ab₁ ac) rewrite det ab ab₁ = [∨]-introᵣ ac

  instance
    deterministic-confluence : Confluence
    deterministic-confluence = intro proof where
      proof : Names.Confluence
      proof {c = c} at ac = [∃]-intro c ⦃ [∧]-intro ac at ⦄
      {-# CATCHALL #-}
      proof {b = b} ab at = [∃]-intro b ⦃ [∧]-intro at ab ⦄
      proof (prepend ab1 ab) (prepend ab2 ac) rewrite det ab1 ab2 = proof ab ac

  deterministic-unique-normalizes-to : ∀{a} → Unique(a normalizes-to_)
  deterministic-unique-normalizes-to (intro ax) (intro ay) = proof ax ay where
    proof : ∀{a b c} → ⦃ _ : NormalForm(b) ⦄ → ⦃ _ : NormalForm(c) ⦄ → Walk(_⟶_) a b → Walk(_⟶_) a c → (b ≡ c)
    proof                          at              at              = [≡]-intro
    proof ⦃ intro normal-x ⦄ ⦃ _ ⦄ at              (prepend ab by) = [⊥]-elim(normal-x ab)
    proof ⦃ _ ⦄ ⦃ intro normal-y ⦄ (prepend ab bx) at              = [⊥]-elim(normal-y ab)
    proof (prepend ab₁ b₁x) (prepend ab₂ b₂y) rewrite det ab₁ ab₂ = proof b₁x b₂y

confluence-semiconfluence : Confluence ↔ Semiconfluence
confluence-semiconfluence = [↔]-intro (semiconfl ↦ intro(l(semiconfl))) r where
  l : Names.Confluence ← Semiconfluence
  l semiconfl at                xc = sub₂(Walk(_⟶_))(Joinable) xc
  l semiconfl (prepend xb₁ b₁b) xc with Semiconfluent.proof semiconfl xb₁ xc
  ... | [∃]-intro d ⦃ [∧]-intro b₁d c₁d ⦄ with l semiconfl b₁b b₁d
  ... | [∃]-intro e ⦃ [∧]-intro be de ⦄ = [∃]-intro e ⦃ [∧]-intro be (transitivity(Walk(_⟶_)) c₁d de) ⦄

  r : Confluence → Semiconfluence
  Semiconfluent.proof (r confl) xb xc = Confluent.proof confl (sub₂(_⟶_)(Walk(_⟶_)) xb) xc

-- TODO: Not sure, but maybe?
{-# TERMINATING #-}
strong-confluence-confluence : StrongConfluence → Confluence
strong-confluence-confluence strconfl = intro(proof strconfl) where
  proof : StrongConfluence → Names.Confluence
  proof strconfl {x} at at = reflexivity(Joinable)
  proof strconfl {x} at (prepend xb bc) = sub₂(Walk(_⟶_))(Joinable) (prepend xb bc)
  proof strconfl {x} (prepend xb₁ b₁b) at = symmetry(Joinable) (sub₂(Walk(_⟶_))(Joinable) (prepend xb₁ b₁b))
  proof strconfl {x} {b}{c} (prepend xb₁ b₁b) (prepend xb₂ b₂c) with StronglyConfluent.proof strconfl xb₁ xb₂
  proof strconfl {x} {b}{c} (prepend xd db) (prepend xb₁ b₁c) | [∃]-intro d ⦃ [∧]-intro refl b₁d ⦄ with proof strconfl b₁c b₁d
  ... | [∃]-intro e ⦃ [∧]-intro ce de ⦄ with proof strconfl db de
  ... | [∃]-intro f ⦃ [∧]-intro bf ef ⦄ = [∃]-intro f ⦃ [∧]-intro bf (transitivity(Walk(_⟶_)) ce ef) ⦄
  proof strconfl {x} {b}{c} (prepend xb₁ b₁b) (prepend xb₂ b₂c) | [∃]-intro d ⦃ [∧]-intro (super b₁d) b₂d ⦄ with proof strconfl b₁b (sub₂(_⟶_)(Walk(_⟶_)) b₁d)
  ... | [∃]-intro e ⦃ [∧]-intro be de ⦄ with proof strconfl b₂c b₂d
  ... | [∃]-intro f ⦃ [∧]-intro cf df ⦄ with proof strconfl de df
  ... | [∃]-intro g ⦃ [∧]-intro eg fg ⦄ = [∃]-intro g ⦃ [∧]-intro (transitivity(Walk(_⟶_)) be eg) (transitivity(Walk(_⟶_)) cf fg) ⦄

semiconfluence-everywhere-common-reduct : ⦃ _ : Semiconfluence ⦄ → EverywhereCommonReduct
semiconfluence-everywhere-common-reduct ⦃ semiconfl ⦄ = intro proof where
  instance
    confl : Confluence
    confl = [↔]-to-[←] confluence-semiconfluence semiconfl

  proof : Names.EverywhereCommonReduct
  proof at = reflexivity(Joinable)
  proof {a}{c} (prepend {b = b} ab bc) = transitivity(Joinable) (sub₂(Walk(_⟶_))(Joinable) (sub₂(_⟶_)(Walk(_⟶_)) ab)) (proof bc)

diamond-property-locally-confluent : ⦃ _ : ∀ₗ(DiamondProperty) ⦄ → LocalConfluence
LocallyConfluent.proof (diamond-property-locally-confluent {x}) xb xc = [∃]-map-proof ([∧]-map (sub₂(_⟶_)(Walk(_⟶_))) (sub₂(_⟶_)(Walk(_⟶_)))) (diamond-property _ xb xc)

-- locally-confluent-diamond-property : ⦃ LocalConfluence ⦄ → ∀ₗ(DiamondProperty)
-- DiamondProperty.proof locally-confluent-diamond-property xb xc = {!locally-confluent _ xb xc!}

-- Terminating ↔ LocalConfluence (TODO: See Newman's lemma)
-- Convergent → ∀{a} → Unique(a normalizes-to_)
-- Confluence → (Walk(_⟶_) x y) → NormalForm(y) → (ReflexiveClosure(_⟶_) x y)
-- Confluence → (Walk(_⟶_) x y) → Unique(NormalForm)
-- Confluence → ∀{a} → Unique(a normalizes-to_)

