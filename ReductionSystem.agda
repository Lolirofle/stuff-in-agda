open import Type

module ReductionSystem {ℓ₁ ℓ₂} {Expr : Type{ℓ₁}} (_⟶_ : Expr → Expr → Type{ℓ₂}) where

import      Lvl
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Relator.Equals
import      Structure.Relator.Names as Names
open import Syntax.Function

-- The relation (_⟶_) is a function on the left argument.
-- In terms of paths, it means that there are no forks on any paths.
Deterministic = ∀{a b c : Expr} → (a ⟶ b) → (a ⟶ c) → (b ≡ c)

-- An expression is reducible when there is an expression it can reduce to.
-- In terms of paths, it means that one can go somewhere else from this point.
Reducible : Expr → Type
Reducible(a) = ∃(a ⟶_)

-- An expression is in normal form when it is irreducible (cannot be reduced any further).
-- In terms of paths, it means that this point is a dead-end.
NormalForm : Expr → Type
NormalForm(a) = ∀{b : Expr} → ¬(a ⟶ b)

-- Note: This is called path because of the interpretation that a binary relation (A → A → Set) is a graph.
data Path : Expr → Expr → Type{ℓ₁ Lvl.⊔ ℓ₂} where
  reflexivity : Names.Reflexivity(Path)
  prepend : ∀{a b c} → (a ⟶ b) → (Path b c) → (Path a c)

-- There is a path between two points when there is one step between them.
Path-super : Names.Subrelation(_⟶_)(Path)
Path-super ab = prepend ab Path.reflexivity

-- Path is a "smallest" reflexive-transitive closure
Path-sub : ∀{ℓ₃}{_▫_ : Expr → Expr → Type{ℓ₃}} → Names.Reflexivity(_▫_) → Names.Transitivity(_▫_) → Names.Subrelation(_⟶_)(_▫_) → Names.Subrelation(Path)(_▫_)
Path-sub refl trans sub reflexivity     = trans refl refl
Path-sub refl trans sub (prepend ab1 pb1b) = trans (sub ab1) (Path-sub refl trans sub pb1b)

-- A path can be concatenated to form a new path.
Path-transitivity : Names.Transitivity(Path)
Path-transitivity reflexivity                sbc  = sbc
Path-transitivity (prepend ab sbb1) sb1c = prepend ab (Path-transitivity sbb1 sb1c)

-- All paths from a dead-end results in going nowhere.
Normal-unique-Path : ∀{a} → NormalForm(a) → ∀{b} → Path a b → (a ≡ b)
Normal-unique-Path na reflexivity = [≡]-intro
Normal-unique-Path na (prepend ab1 sb1b) = [⊥]-elim(na ab1)

-- "a normalizes to b" means that "a" reduces to the normal form "b".
-- In terms of paths, this means that the dead end of one path from "a" is "b".
_normalizes-to_ : Expr → Expr → Type
_normalizes-to_ a b = (Path a b) ∧ NormalForm(b)

-- In terms of paths, this means that there is a path which leads to a dead-end.
Normalizes : Expr → Type
Normalizes a = ∃(a normalizes-to_)

-- A reduction system is normalizing when all expressions in the language have a normal form.
-- In terms of paths, this means that all points eventually lead to dead-ends.
Normalizing = ∃{Obj = Expr → Expr} (normal ↦ ∀{e} → (e normalizes-to (normal e)))

-- Reflexive-transitive closure of a relation
-- Sometimes also notated (_▫*_) for a relation (_▫_)
data ReflexiveTransitiveClosure : Expr → Expr → Type{ℓ₁ Lvl.⊔ ℓ₂} where
  reflexivity  : Names.Reflexivity(ReflexiveTransitiveClosure)
  super        : Names.Subrelation(_⟶_)(ReflexiveTransitiveClosure)
  transitivity : Names.Transitivity(ReflexiveTransitiveClosure)

-- The "prepend"-property of reflexive-transitive closure
ReflexiveTransitiveClosure-prepend : ∀{a b c} → (a ⟶ b) → ReflexiveTransitiveClosure b c → ReflexiveTransitiveClosure a c
ReflexiveTransitiveClosure-prepend ab bc = transitivity (super ab) bc

-- A reflexive-transitive closure is the same as a path.
ReflexiveTransitiveClosure-Path-equivalence : ∀{a b} → (ReflexiveTransitiveClosure a b) ↔ (Path a b)
ReflexiveTransitiveClosure-Path-equivalence = [↔]-intro l r where
  r : ∀{a b} → ReflexiveTransitiveClosure a b → Path a b
  r ReflexiveTransitiveClosure.reflexivity              = Path.reflexivity
  r (ReflexiveTransitiveClosure.super ab)               = Path-super ab
  r (ReflexiveTransitiveClosure.transitivity rab1 rb1b) = Path-transitivity (r rab1) (r rb1b)

  l : ∀{a b} → Path a b → ReflexiveTransitiveClosure a b
  l Path.reflexivity        = ReflexiveTransitiveClosure.reflexivity
  l (Path.prepend ab1 sb1b) = ReflexiveTransitiveClosure-prepend ab1 (l sb1b)

-- Both a and b reduce to the same expression in zero or more steps.
-- In terms of paths, this means that paths starting from the two points are able to eventually meet.
-- TODO: What is Joinable?
CommonReduct : Expr → Expr → Type
CommonReduct a b = ∃(c ↦ (Path a c) ∧ (Path b c))

-- An expression reduces to itself in zero steps.
-- In terms of paths, this means that two paths starting from the same point can reach this same point.
CommonReduct-reflexivity : Names.Reflexivity(CommonReduct)
∃.witness (CommonReduct-reflexivity {x}) = x
∃.proof   (CommonReduct-reflexivity {x}) = [∧]-intro Path.reflexivity Path.reflexivity

-- When one reduces to the same expression as the other, the other also reduces to the same expression as the first one.
CommonReduct-symmetry : Names.Symmetry(CommonReduct)
∃.witness (CommonReduct-symmetry {x} {y} xy) = [∃]-witness xy
∃.proof   (CommonReduct-symmetry {x} {y} xy) = [∧]-intro ([∧]-elimᵣ(∃.proof xy)) (([∧]-elimₗ(∃.proof xy)))

-- An expression is confluent when all its reducts have a common reduct.
-- In terms of paths, this means that paths starting from this point can always eventually meet.
Confluent : Expr → Type
Confluent a = ∀{b c} → (Path a b) → (Path a c) → CommonReduct b c

-- All expressions are confluent.
-- In terms of paths, this means that parts starting from the same point can always eventually meet.
Confluence = ∀{a} → Confluent(a)

Confluence-to-CommonReduct-transitivity : Confluence → Names.Transitivity(CommonReduct)
Confluence-to-CommonReduct-transitivity confl {x}{y}{z} ([∃]-intro obj-xy ⦃ [∧]-intro pxxy pyxy ⦄) ([∃]-intro obj-yz ⦃ [∧]-intro pyyz pzyz ⦄) = [∃]-intro obj ⦃ [∧]-intro l r ⦄ where
  objxy-objyz-common-reduct : CommonReduct obj-xy obj-yz
  objxy-objyz-common-reduct = confl pyxy pyyz

  obj : Expr
  obj = [∃]-witness objxy-objyz-common-reduct

  l : Path x obj
  l = Path-transitivity pxxy ([∧]-elimₗ ([∃]-proof objxy-objyz-common-reduct))

  r : Path z obj
  r = Path-transitivity pzyz ([∧]-elimᵣ ([∃]-proof objxy-objyz-common-reduct))

-- Confluence-to-CommonReduct-equivalence : Confluence → Equivalence(CommonReduct)

-- Terminating = WellFounded ∘ converse

module _ (det : Deterministic) where
  -- Frege thing
  deterministic-dichotomy : ∀{a b c} → (Path a b) → (Path a c) → (Path b c) ∨ (Path c b)
  deterministic-dichotomy reflexivity ac = [∨]-introₗ ac
  deterministic-dichotomy (ab @ (prepend _ _)) reflexivity = [∨]-introᵣ ab
  deterministic-dichotomy (prepend ab2 b) (prepend ab3 ac) with det ab2 ab3
  ... | [≡]-intro = deterministic-dichotomy b ac

  deterministic-confluence : Deterministic → Confluence
  deterministic-confluence det {c = c} reflexivity ac = [∃]-intro c ⦃ [∧]-intro ac reflexivity ⦄
  deterministic-confluence det {b = b} ab reflexivity = [∃]-intro b ⦃ [∧]-intro reflexivity ab ⦄
  deterministic-confluence det (prepend ab1 ab) (prepend ab2 ac) rewrite det ab1 ab2 = deterministic-confluence det ab ac

  -- Normal(b) → Normal(c) → (Path a b) → (Path a c) → (b ≡ c)

  -- deterministic-normalizes-to : Deterministic(_normalizes-to_)
