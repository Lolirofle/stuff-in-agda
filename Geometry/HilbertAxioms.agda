-- TODO: Unfinished
open import Logic
open import Type
open import Structure.Relator
open import Structure.Setoid.WithLvl

module Geometry.HilbertAxioms
  {ℓₚ ℓₗ ℓₚₑ ℓₗₑ ℓₚₗ ℓₚₚₚ}
  (Point : Type{ℓₚ}) ⦃ equiv-point : Equiv{ℓₚₑ}(Point) ⦄ -- The type of points on a plane.
  (Line : Type{ℓₗ}) ⦃ equiv-line : Equiv{ℓₗₑ}(Line) ⦄    -- The type of lines on a plane.
  (Distance : Type{ℓₗ}) ⦃ equiv-distance : Equiv{ℓₗₑ}(Distance) ⦄
  (Angle : Type{ℓₗ}) ⦃ equiv-angle : Equiv{ℓₗₑ}(Angle) ⦄
  (_∈ₚₗ_ : Point → Line → Stmt{ℓₚₗ})                     -- `p ∈ₚₗ l` means that the point `p` lies on the line `l`.
  (_―_―_ : Point → Point → Point → Stmt{ℓₚₚₚ})           -- `p₁ ― p₂ ― p₃` means that the second point `p₂` lies between `p₁` and `p₃` in some line.
  ⦃ incidence-relator : BinaryRelator(_∈ₚₗ_) ⦄
  ⦃ betweenness-relator : TrinaryRelator(_―_―_) ⦄
  where

open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Functional.Combinations
import      Lvl
open import Logic.Predicate
open import Logic.Propositional
open import Logic.Propositional.Xor
open import Sets.ExtensionalPredicateSet renaming (_≡_ to _≡ₛ_)
open import Structure.Relator.Properties
open import Structure.Setoid.Uniqueness
open import Syntax.Function

private variable p p₁ p₂ p₃ p₄ q q₁ q₂ q₃ q₄ : Point
private variable l l₁ l₂ : Line

module _ where
  -- An open line segment.
  -- The set of points strictly between two points in a line.
  -- Also called:
  -- • Open interval in A Minimal Version of Hilbert's Axioms for Plane Geometry by William Richter.
  betweens : Point → Point → PredSet(Point)
  betweens a b ∋ p = a ― p ― b
  PredSet.preserve-equiv (betweens a b) = TrinaryRelator.unary₂ betweenness-relator

  extensionPoints : Point → Point → PredSet(Point)
  extensionPoints a b ∋ p = a ― b ― p
  PredSet.preserve-equiv (extensionPoints a b) = TrinaryRelator.unary₃ betweenness-relator

  -- A line segment.
  -- The set of points between two points in a line including the endpoints.
  segment : Point → Point → PredSet(Point)
  segment a b = (• a) ∪ (• b) ∪ (betweens a b)

  -- A ray.
  -- The set of points between starting from `a` in the direction of `b` in a line.
  ray : Point → Point → PredSet(Point)
  ray a b = (• a) ∪ (• b) ∪ (extensionPoints a b)

  angle : Point → Point → Point → PredSet(PredSet(Point))
  angle p₁ p₂ p₃ = (• ray p₁ p₂) ∪ (• ray p₁ p₃)

Distinct₃ : Point → Point → Point → Stmt
Distinct₃ = combine₃Fn₂Op₂(_≢_)(_∧_)

Collinear₃ : Point → Point → Point → Stmt
Collinear₃ p₁ p₂ p₃ = ∃(l ↦ all₃Fn₁Op₂(_∈ₚₗ l)(_∧_) p₁ p₂ p₃)

record Axioms : Type{ℓₚ Lvl.⊔ ℓₗ Lvl.⊔ ℓₚₑ Lvl.⊔ ℓₗₑ Lvl.⊔ ℓₚₗ Lvl.⊔ ℓₚₚₚ} where
  field
    -- There is an unique line for every unordered distinct pair of points.
    -- Also called:
    -- • I1 in Hilbert’s Axiom System for Plane Geometry, A Short Introduction by Bjørn Jahren.
    -- • I.1 and I.2 in Project Gutenberg’s The Foundations of Geometry by David Hilbert.
    -- • I1 in A Minimal Version of Hilbert's Axioms for Plane Geometry by William Richter.
    line-construction : (p₁ ≢ p₂) → ∃!(l ↦ (p₁ ∈ₚₗ l) ∧ (p₂ ∈ₚₗ l))

    -- There are two distinct points on every line.
    -- Also called:
    -- • I2 in Hilbert’s Axiom System for Plane Geometry, A Short Introduction by Bjørn Jahren.
    -- • I.7 in Project Gutenberg’s The Foundations of Geometry by David Hilbert.
    -- • I2 in A Minimal Version of Hilbert's Axioms for Plane Geometry by William Richter.
    line-deconstruction : ∃{Obj = Point ⨯ Point}(\{(p₁ , p₂) → (p₁ ≢ p₂) ∧ (p₁ ∈ₚₗ l) ∧ (p₂ ∈ₚₗ l)})

    -- There exists three points that constructs a triangle (not all on the same line).
    -- • I3 in Hilbert’s Axiom System for Plane Geometry, A Short Introduction by Bjørn Jahren.
    -- • I3 in A Minimal Version of Hilbert's Axioms for Plane Geometry by William Richter.
    triangle-existence : ∃{Obj = Point ⨯ Point ⨯ Point}(\{(p₁ , p₂ , p₃) → ¬(Collinear₃ p₁ p₂ p₃)})

    -- The betweenness relation is strict (pairwise irreflexive).
    -- There are no points between a single point.
    betweenness-strictness : ¬(p₁ ― p₂ ― p₁)

    -- The betweenness relation is symmetric.
    -- Also called:
    -- • B1 in Hilbert’s Axiom System for Plane Geometry, A Short Introduction by Bjørn Jahren.
    -- • II.1 in Project Gutenberg’s The Foundations of Geometry by David Hilbert.
    -- • B1 in A Minimal Version of Hilbert's Axioms for Plane Geometry by William Richter.
    betweenness-symmetry : (p₁ ― p₂ ― p₃) → (p₃ ― p₂ ― p₁)

    -- A line segment can be extended to a third point.
    -- • Part of II.2 in Project Gutenberg’s The Foundations of Geometry by David Hilbert.
    -- • B2 in Hilbert’s Axiom System for Plane Geometry, A Short Introduction by Bjørn Jahren.
    -- • B2 in A Minimal Version of Hilbert's Axioms for Plane Geometry by William Richter.
    betweenness-extensionᵣ : (p₁ ≢ p₂) → ∃(p₃ ↦ (p₁ ― p₂ ― p₃))

    -- Three points are always between each other in a certain order.
    betweenness-antisymmetryₗ : (p₁ ― p₂ ― p₃) → (p₂ ― p₁ ― p₃) → ⊥

    -- Three distinct points on a line are always between each other in a certain order.
    -- Also called:
    -- • Part of B3 in Hilbert’s Axiom System for Plane Geometry, A Short Introduction by Bjørn Jahren.
    -- • Part of II.3 in Project Gutenberg’s The Foundations of Geometry by David Hilbert.
    -- • Part of B3 in A Minimal Version of Hilbert's Axioms for Plane Geometry by William Richter.
    betweenness-cases : (Distinct₃ p₁ p₂ p₃) → (Collinear₃ p₁ p₂ p₃) → (rotate₃Fn₃Op₂(_―_―_)(_∨_) p₁ p₂ p₃)

    -- For three points that forms a triangle, and a line not intersecting the triangle's vertices, but intersecting one of its edges. Such a line intersects exactly one of the other edges of the triangle.
    -- Also called:
    -- • Pasch's axiom
    -- • B4 in Hilbert’s Axiom System for Plane Geometry, A Short Introduction by Bjørn Jahren.
    -- • II.5 in Project Gutenberg’s The Foundations of Geometry by David Hilbert.
    -- • B4 in A Minimal Version of Hilbert's Axioms for Plane Geometry by William Richter.
    line-triangle-intersection : ¬(Collinear₃ p₁ p₂ p₃) → (all₃Fn₁Op₂(¬_ ∘ (_∈ₚₗ l))(_∧_) p₁ p₂ p₃) → ((p ∈ₚₗ l) ∧ (p₁ ― p ― p₂)) → (∃(p ↦ (p ∈ₚₗ l) ∧ (p₁ ― p ― p₃)) ⊕ ∃(p ↦ (p ∈ₚₗ l) ∧ (p₂ ― p ― p₃)))

    -- TODO: The rest of the axioms are not yet formulated because I am not sure what the best way to express them is
    ray-segment : ∃!(p ↦ (p ∈ ray p₁ p₂) ∧ (segment q₁ q₂ ≡ₛ segment p₁ p))
    segment-concat : (p₁ ― p₂ ― p₃) → (q₁ ― q₂ ― q₃) → (segment p₁ p₂ ≡ₛ segment q₁ q₂) → (segment p₂ p₃ ≡ₛ segment q₂ q₃) → (segment p₁ p₃ ≡ₛ segment q₁ q₃)

  -- A pair of points constructs a line.
  line : (a : Point) → (b : Point) → (a ≢ b) → Line
  line a b nab = [∃!]-witness(line-construction nab)

  -- A line can be deconstructed to two points.
  linePoints : Line → (Point ⨯ Point)
  linePoints l = [∃]-witness(line-deconstruction{l})

  -- The point to the left in the construction of a line is in the line.
  line-construction-pointₗ : (np12 : p₁ ≢ p₂) → (p₁ ∈ₚₗ line p₁ p₂ np12)
  line-construction-pointₗ np12 = [∧]-elimₗ([∃!]-proof (line-construction np12))

  -- The point to the right in the construction of a line is in the line.
  line-construction-pointᵣ : (np12 : p₁ ≢ p₂) → (p₂ ∈ₚₗ line p₁ p₂ np12)
  line-construction-pointᵣ np12 = [∧]-elimᵣ([∃!]-proof (line-construction np12))

  -- Two lines having a pair of common points are the same line..
  line-uniqueness : (p₁ ≢ p₂) → (p₁ ∈ₚₗ l₁) → (p₂ ∈ₚₗ l₁) → (p₁ ∈ₚₗ l₂) → (p₂ ∈ₚₗ l₂) → (l₁ ≡ l₂)
  line-uniqueness np12 p1l1 p2l1 p1l2 p2l2 = [∃!]-uniqueness (line-construction np12) ([∧]-intro p1l1 p2l1) ([∧]-intro p1l2 p2l2)

  -- The deconstructed points of a line are distinct.
  linePoints-distinct : let (a , b) = linePoints(l) in (a ≢ b)
  linePoints-distinct = [∧]-elimₗ([∧]-elimₗ([∃]-proof(line-deconstruction)))

  -- The left deconstructed point of a line is in the line.
  linePoints-pointₗ : Tuple.left(linePoints(l)) ∈ₚₗ l
  linePoints-pointₗ = [∧]-elimᵣ([∧]-elimₗ([∃]-proof(line-deconstruction)))

  -- The right deconstructed point of a line is in the line.
  linePoints-pointᵣ : Tuple.right(linePoints(l)) ∈ₚₗ l
  linePoints-pointᵣ = [∧]-elimᵣ([∃]-proof(line-deconstruction))

  -- The line of the deconstructed points of a line is the same line.
  line-linePoints-inverseᵣ : let (a , b) = linePoints(l) in (line a b linePoints-distinct ≡ l)
  line-linePoints-inverseᵣ = line-uniqueness
    linePoints-distinct (line-construction-pointₗ linePoints-distinct) (line-construction-pointᵣ linePoints-distinct) linePoints-pointₗ linePoints-pointᵣ



  betweenness-antisymmetryᵣ : (p₁ ― p₂ ― p₃) → (p₁ ― p₃ ― p₂) → ⊥
  betweenness-antisymmetryᵣ p123 p132 = betweenness-antisymmetryₗ (betweenness-symmetry p123) (betweenness-symmetry p132)

  betweenness-irreflexivityₗ : ¬(p₁ ― p₁ ― p₂)
  betweenness-irreflexivityₗ p112 = betweenness-antisymmetryₗ p112 p112

  betweenness-irreflexivityᵣ : ¬(p₁ ― p₂ ― p₂)
  betweenness-irreflexivityᵣ p122 = betweenness-irreflexivityₗ (betweenness-symmetry p122)

  -- Also called:
  -- • B1 in Hilbert’s Axiom System for Plane Geometry, A Short Introduction by Bjørn Jahren.
  -- • B1 in A Minimal Version of Hilbert's Axioms for Plane Geometry by William Richter.
  betweenness-distinct : (p₁ ― p₂ ― p₃) → (Distinct₃ p₁ p₂ p₃)
  Tuple.left              (betweenness-distinct p123)  p12 = betweenness-irreflexivityₗ(substitute₃-unary₁(_―_―_) p12 p123)
  Tuple.left (Tuple.right (betweenness-distinct p123)) p13 = betweenness-strictness(substitute₃-unary₁(_―_―_) p13 p123)
  Tuple.right(Tuple.right (betweenness-distinct p123)) p23 = betweenness-irreflexivityᵣ(substitute₃-unary₂(_―_―_) p23 p123)

  betweenness-extensionₗ : (p₂ ≢ p₃) → ∃(p₁ ↦ (p₁ ― p₂ ― p₃))
  betweenness-extensionₗ np23 = [∃]-map-proof betweenness-symmetry (betweenness-extensionᵣ (np23 ∘ symmetry(_≡_)))

  -- Three points are always between each other in a certain order.
    -- Also called:
    -- • B3 in Hilbert’s Axiom System for Plane Geometry, A Short Introduction by Bjørn Jahren.
    -- • II.3 in Project Gutenberg’s The Foundations of Geometry by David Hilbert.
    -- • B3 in A Minimal Version of Hilbert's Axioms for Plane Geometry by William Richter.
  betweenness-distinct-cases : (Distinct₃ p₁ p₂ p₃) → (Collinear₃ p₁ p₂ p₃) → ((p₁ ― p₂ ― p₃) ⊕₃ (p₂ ― p₃ ― p₁) ⊕₃ (p₃ ― p₁ ― p₂))
  betweenness-distinct-cases pd pl with betweenness-cases pd pl
  ... | [∨]-introₗ             p123  = [⊕₃]-intro₁ p123 (betweenness-antisymmetryₗ (betweenness-symmetry p123)) (betweenness-antisymmetryᵣ (betweenness-symmetry p123))
  ... | [∨]-introᵣ ([∨]-introₗ p231) = [⊕₃]-intro₂ (betweenness-antisymmetryᵣ ((betweenness-symmetry p231))) p231 (betweenness-antisymmetryₗ ((betweenness-symmetry p231)))
  ... | [∨]-introᵣ ([∨]-introᵣ p312) = [⊕₃]-intro₃ (betweenness-antisymmetryₗ (betweenness-symmetry p312)) (betweenness-antisymmetryᵣ (betweenness-symmetry p312)) p312

  --betweenness-between : (p₁ ≢ p₂) → (p₁ ∈ₚₗ l) → (p₂ ∈ₚₗ l) → ∃(p ↦ p₁ ― p ― p₂)
  --betweenness-between np12 p1l p2l = {!!}

  --betweenness-collinnear : (p₁ ― p₂ ― p₃) → (Collinear₃ p₁ p₂ p₃)
