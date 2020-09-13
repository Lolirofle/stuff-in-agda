open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Logic.Classical
open import Logic
import      Lvl
open import Type
open import Structure.Setoid.WithLvl

-- Elementary Plane Geometry.
-- An axiomatic approach to plane geometry in first order logic.
-- The axiomatic system used here is usually called "Tarski's axioms", and plane geometry is also known as two-dimensional Euclidean geometry.
module Geometry.Axioms
  {ℓₚ ℓₚₑ ℓₗₗₑ ℓₗᵢₗ}
  (Point : Type{ℓₚ}) ⦃ Point-equiv : Equiv{ℓₚₑ}(Point) ⦄
  (Equidistanced : (Point ⨯ Point) → (Point ⨯ Point) → Stmt{ℓₗₗₑ}) -- Two pairs of points have the same distance between each other.
  (Aligned : Point → Point → Point → Stmt{ℓₗᵢₗ})                   -- Three points are aligned in a weak order. The second point is between the first and the third in a line.
  ⦃ classical : ∀{ℓ}{P : Stmt{ℓ}} → Classical(P) ⦄
  where

open import Data.Tuple.Equiv
open import Functional
open import Functional.Combinations
open import Logic.Predicate
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Sets.ExtensionalPredicateSet renaming (_≡_ to _≡ₛ_)
open import Structure.Relator.Equivalence
open import Structure.Relator.Ordering
open import Structure.Relator.Properties
open import Structure.Relator
open import Structure.Setoid.Uniqueness
open import Syntax.Function
open import Syntax.Implication
open import Syntax.Transitivity
open import Syntax.Type

private variable ℓ ℓ₁ ℓ₂ ℓₗ ℓₗ₁ ℓₗ₂ : Lvl.Level
private variable p a b c d e p₁ p₂ pᵢ pₒ pᵣ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂ i m₁ m₂ : Point
private variable P Q : Point → Stmt{ℓ}

-- Three points are aligned in a strict order. The second point is between the first and the third in a line without being the first or the second.
Between : Point → Point → Point → Stmt
Between a b c = (Aligned a b c) ∧ ((a ≢ b) ∧ (b ≢ c))

-- Three points are collinear when they all are points of a single line.
Collinear : Point → Point → Point → Stmt
Collinear a b c = (Aligned a b c) ∨ (Aligned b c a) ∨ (Aligned c a b)

Aligned₄ : Point → Point → Point → Point → Stmt
Aligned₄ = combine₄Fn₃Op₂ Aligned (_∧_)

-- The equivalence on points.
_≡ₚ_ = Equiv._≡_ Point-equiv

-- Source: Tarski's axioms of geometry (https://en.wikipedia.org/wiki/Tarski%27s_axioms @ 2020-06-14).
-- TODO: Are there any modifications of the axioms when working in constructive logic?
record Axioms : Typeω where
  field
    ⦃ Equidistanced-relator ⦄ : BinaryRelator(Equidistanced)
    ⦃ Aligned-relator ⦄ : TrinaryRelator(Aligned)
    -- ⦃ Point-equivalence-classical ⦄ : Classical₂(_≡ₚ_)
    -- ⦃ Equidistanced-classical ⦄ : Classical₂(Equidistanced)
    -- ⦃ Aligned-classical ⦄ : Classical₃(Aligned)

    -- The distance between p₁ and p₂ is the same as the distance between p₂ and p₁.
    -- The order of the points in the equidistance relation does not matter.
    -- Example:
    --   • (p₁) <--- (p₂)
    --   • (p₁) ---> (p₂)
    --   These two drawings depict lines between points p₁ and p₂. They have the same length.
    --   So there is no need to draw an arrow head on the lines when referring to the length of a line.
    -- Also called: A1 in Metamathematische Methoden in der Geometrie.
    Equidistanced-flipped : Equidistanced(p₁ , p₂)(p₂ , p₁)

    -- Equidistance is a transitive relation.
    -- Example:
    --   la: (a₁) ---- (a₂)
    --   lb: (b₁) ---- (b₂)
    --   lc: (c₁) ---- (c₂)
    --   Here is a drawing of three lines.
    --   The line la have the same length as lb, and the line la have the same length as lc. Then lb have the same length as lc.
    -- Also called: A2 in Metamathematische Methoden in der Geometrie.
    Equidistanced-symmetric-transitivity : Equidistanced(a₁ , a₂)(b₁ , b₂) → Equidistanced(a₁ , a₂)(c₁ , c₂) → Equidistanced(b₁ , b₂)(c₁ , c₂)

    -- If two points have the same distance as the distance between a single point with itself, then they are the same point.
    -- Essentially, if two points have no distance between each other, they are the same point.
    -- Example:
    --   (p₁) ---------- (p₂)
    --   (p)
    --   Here p₁ and p₂ are arbitrary points, and a line between them is depicted.
    --   The line from p to p is also depicted (as a point).
    --   Currently, these lines do not have the same length, and for p₁ and p₂ to have the same distance as the single point line consisting of p, the line must collapse to a single point, making p₁ and p₂ the same point.
    -- Also called:
    -- • Identity axiom for the `Equidistance` relation.
    -- • A3 in Metamathematische Methoden in der Geometrie.
    Equidistanced-point : Equidistanced(p₁ , p₂)(p , p) → (p₁ ≡ p₂)

    -- Given two lines, there exists a line extending the first line so that the extension part is of the same length as the second line.
    -- Essentially, given a starting point and a direction, it is always possible to construct a line of the same length as an another already existing line.
    -- Or: It is always possible to extend a line by the length of another line.
    -- Example:
    --   Given two lines:
    --   (p) <-- (a₁)
    --   (a₂) ------> (b₂)
    --   it is possible to construct an extension of the first line like this:
    --   (b₁) <------(p)-- (a₁)
    --   The extension from a₁ to b₁ have the same direction as the first line (a₁ to p) and the same length as the second line (from a₂ to b₂).
    -- Also called:
    -- • A4 in Metamathematische Methoden in der Geometrie.
    segment-construction : ∃(b₁ ↦ (Aligned a₁ p b₁) ∧ Equidistanced(p , b₁)(a₂ , b₂))

    -- Given two bisected triangles, if all except one of the non-bisected sides of the first triangle have the same length as the second one's, then the unknown side of the first triangle is also congruent to the unknown side of the second.
    -- 
    -- Note: If any of the points other than (a,b) or (a,d) are equal, then the result follows from the assumptions.
    --         (d)\__
    --        /  \_  \__
    --      /      \_   \__
    --    /          \     \
    --  (a)__________(b)___(c)
    --
    -- Also called:
    -- • A5 in Metamathematische Methoden in der Geometrie.
    five-segment : (a₁ ≢ b₁) → (Aligned a₁ b₁ c₁) → (Aligned a₂ b₂ c₂) → Equidistanced(a₁ , b₁)(a₂ , b₂) → Equidistanced(b₁ , c₁)(b₂ , c₂) → Equidistanced(a₁ , d₁)(a₂ , d₂) → Equidistanced(b₁ , d₁)(b₂ , d₂) → Equidistanced(c₁ , d₁)(c₂ , d₂)

    -- If a point is between two identical points, then they are the same point.
    -- Alternatively, if a point is in a line consisting of only a single point, then the point is the single point.
    -- Example:
    --   (p₁) ------(a)--- (p₂)
    --   Here, a line from p₁ to p₂ is depicted, and a point a is in this line.
    --   But if p₁ and p₂ would be the same point p, then the line would collapse to a single point, making a and p the same.
    -- Also called:
    -- • Identity axiom for the `Aligned` relation.
    -- • A6 in Metamathematische Methoden in der Geometrie.
    Aligned-point : (Aligned p a p) → (a ≡ p)

    -- Given two connected lines and one point in each of the lines, two lines connecting the points and the endpoints of the other line have an intersection point.
    -- Example:
    --         (c)
    --       /     \
    --    (m₁)\   /(m₂)
    --    /   _(i)_   \
    --  (a)__/     \__(b)
    -- Also called:
    -- • Axiom of Pasch.
    -- • Inner Pasch.
    -- • A7 in Metamathematische Methoden in der Geometrie.
    Aligned-intersection : (Aligned a m₁ c) → (Aligned b m₂ c) → ∃(i ↦ (Aligned m₁ i b) ∧ (Aligned m₂ i a))

    -- Also called:
    -- • Axiom schema of Continuity
    -- • A11' in Metamathematische Methoden in der Geometrie.
    Aligned-continuity : ∃(a ↦ ∀{x y} → P(x) → Q(y) → (Aligned a x y)) → ∃(a ↦ ∀{x y} → P(x) → Q(y) → (Aligned x a y))

    -- A triangle exists.
    -- This excludes the possibility of this theory describing 0 or 1-dimensional spaces when using the standard interpretation of the axioms.
    -- Example:
    --    (c)
    --   /   \
    -- (a)___(b)
    -- Also called:
    -- • A8 in Metamathematische Methoden in der Geometrie.
    lower-dimension₂ : ∃{Obj = Point ⨯ Point ⨯ Point}(\(a , b , c) → (¬ Aligned a b c) ∧ (¬ Aligned b c a) ∧ (¬ Aligned c a b))

    -- Also called:
    -- • A9 in Metamathematische Methoden in der Geometrie.
    upper-dimension₂ : Equidistanced(a , p₁)(a , p₂) → Equidistanced(b , p₁)(b , p₂) → Equidistanced(c , p₁)(c , p₂) → (p₁ ≢ p₂) → (Aligned a b c) ∨ (Aligned b c a) ∨ (Aligned c a b)

    -- Given three points, they are either collinear (forming a line), or there is a circumcentered point for the triangle of the three points (a point where the distance between this point and all three vertices are equal).
    -- Example:
    --   Here is an example of the different cases depicted:
    --   • (a) ----(b)------ (c)
    --   • (b) ----(c)------ (a)
    --   • (c) ----(a)------ (b)
    --   •      (a)\__
    --         /  ‖   \__
    --       /     ‖      \
    --     (b)______‖______(c)
    --       \___   ‖  ___/
    --           \_(m)_/
    --     or when the triangle is equilateral:
    --        (a)
    --        / \
    --       /   \
    --      / (m) \
    --     /_______\
    --   (b)       (c)
    -- Also called:
    -- • Axiom of Euclid.
    -- • Variant of A10 in Metamathematische Methoden in der Geometrie.
    center-of-3 : (Collinear a b c) ∨ ∃(m ↦ Equidistanced(a , m)(b , m) ∧ Equidistanced(a , m)(c , m))

module _ ⦃ axioms : Axioms ⦄ where
  open Axioms(axioms)

  -- A line constructed by the points `a` and `b` have an intersection point on a circle with the center point `c` and radius point `pᵣ` when a part of the line.
  -- Also called:
  -- • CA in Metamathematische Methoden in der Geometrie.
  -- circle-line-intersection : (Aligned₄ c pᵢ pᵣ pₒ) → Equidistanced(c , a)(c , pᵢ) → Equidistanced(c , b)(c , pₒ) → ∃(i ↦ Equidistanced(c , i)(c , pᵣ) ∧ (Aligned a i b))

  instance
    -- Identical pairs of points have the same distance between each other.
    -- Also called: 2.1 in Metamathematische Methoden in der Geometrie.
    Equidistanced-reflexivity : Reflexivity(Equidistanced)
    Reflexivity.proof Equidistanced-reflexivity {p₁ , p₂} = Equidistanced-symmetric-transitivity (Equidistanced-flipped {p₂}{p₁}) (Equidistanced-flipped {p₂}{p₁})

  instance
    -- Also called: 2.2 in Metamathematische Methoden in der Geometrie.
    Equidistanced-symmetry : Symmetry(Equidistanced)
    Symmetry.proof Equidistanced-symmetry p = Equidistanced-symmetric-transitivity p (reflexivity(Equidistanced))

  instance
    -- Also called: 2.3 in Metamathematische Methoden in der Geometrie.
    Equidistanced-transitivity : Transitivity(Equidistanced)
    Transitivity.proof Equidistanced-transitivity p q = Equidistanced-symmetric-transitivity (symmetry(Equidistanced) p) q

  instance
    -- Also called: 2.7 in Metamathematische Methoden in der Geometrie.
    Equidistanced-equivalence : Equivalence(Equidistanced)
    Equidistanced-equivalence = intro

  -- The distance between a point and itself is the same for all points.
  -- Also called: 2.8 in Metamathematische Methoden in der Geometrie.
  Equidistanced-points : Equidistanced(a , a) (b , b)
  Equidistanced-points {a}{b}
    with [∃]-intro p ⦃ [∧]-intro _ bpaa ⦄ ← segment-construction{a}{b} {a}{a}
    =
      • (b ≡ b) ∧ (p ≡ b)            :-[ [∧]-intro (reflexivity(_≡_)) (symmetry(_≡_) (Equidistanced-point bpaa)) ]
      • Equidistanced(b , p) (b , p) :-[ reflexivity(Equidistanced) ]
      ⇒₂-[ substitute₂ᵣ(Equidistanced) ]
      Equidistanced(b , p) (b , b) ⇒-[ Equidistanced-symmetric-transitivity bpaa ]
      Equidistanced(a , a) (b , b) ⇒-end

  -- Addition of two distances when the points are in a line.
  -- Also called: 2.11 in Metamathematische Methoden in der Geometrie.
  segment-sum : (Aligned a₁ b₁ c₁) → (Aligned a₂ b₂ c₂) → Equidistanced(a₁ , b₁)(a₂ , b₂) → Equidistanced(b₁ , c₁)(b₂ , c₂) → Equidistanced(a₁ , c₁)(a₂ , c₂)
  segment-sum {a₁ = a₁}{b₁ = b₁} abc₁ abc₂ ab₁ab₂ bc₁bc₂ with excluded-middle(a₁ ≡ b₁)
  ... | [∨]-introₗ a₁b₁
    with a₂b₂ ← Equidistanced-point (symmetry(Equidistanced) (substitute₂ₗ(Equidistanced) ([∧]-intro a₁b₁ (reflexivity(_≡ₚ_))) ab₁ab₂))
    = substitute₂(Equidistanced) ([∧]-intro (symmetry(_≡ₚ_) a₁b₁) (reflexivity(_≡ₚ_))) ([∧]-intro (symmetry(_≡ₚ_) a₂b₂) (reflexivity(_≡ₚ_))) bc₁bc₂
  ... | [∨]-introᵣ na₁b₁ =
    Equidistanced-flipped
    🝖 (five-segment
      na₁b₁
      abc₁
      abc₂
      ab₁ab₂
      bc₁bc₂
      Equidistanced-points
      (Equidistanced-flipped 🝖 ab₁ab₂ 🝖 Equidistanced-flipped)
    )
    🝖 Equidistanced-flipped

  -- The segment extension axiom constructs unique points when the given pair of points forms a line segment to extend.
  -- Also called: 2.12 in Metamathematische Methoden in der Geometrie.
  segment-construction-uniqueness : (a₁ ≢ p) → Unique(b₁ ↦ (Aligned a₁ p b₁) ∧ Equidistanced(p , b₁)(a₂ , b₂))
  segment-construction-uniqueness na₁p ([∧]-intro al-a₁p₁x eq-p₁xa₂b₂) ([∧]-intro al-a₁p₁y eq-p₁ya₂b₂)
    with pxpy ← transitivity(Equidistanced) eq-p₁xa₂b₂ (symmetry(Equidistanced) eq-p₁ya₂b₂)
    with a₁xa₁y ← segment-sum al-a₁p₁x al-a₁p₁y (reflexivity(Equidistanced)) pxpy
    = Equidistanced-point (five-segment na₁p al-a₁p₁x al-a₁p₁y (reflexivity(Equidistanced)) pxpy (reflexivity(Equidistanced)) (reflexivity(Equidistanced)))

  -- Two points are always aligned.
  -- Also called: 3.1 in Metamathematische Methoden in der Geometrie.
  Aligned-reflexivityᵣ : Aligned a b b
  Aligned-reflexivityᵣ {a}{b}
    with [∃]-intro p ⦃ [∧]-intro alig equi ⦄ ← segment-construction{a}{b} {a}{a}
    = substitute₃-unary₃(Aligned) (symmetry(_≡_) (Equidistanced-point equi)) alig

  -- A single point is always aligned with itself.
  Aligned-reflexivity : Aligned a a a
  Aligned-reflexivity = Aligned-reflexivityᵣ

  -- When three points are aligned in one direction, they are also aligned in the opposite direction.
  -- Also called: 3.2 in Metamathematische Methoden in der Geometrie.
  Aligned-symmetry : Aligned a b c → Aligned c b a
  Aligned-symmetry {a}{b}{c} alig
    with [∃]-intro p ⦃ [∧]-intro bpb cpa ⦄ ← Aligned-intersection{a}{b}{_}{b}{c} alig Aligned-reflexivityᵣ
    with pb ← Aligned-point bpb
    = substitute₃-unary₂(Aligned) pb cpa

  -- Two points are always aligned.
  -- Also called: 3.3 in Metamathematische Methoden in der Geometrie.
  Aligned-reflexivityₗ : Aligned a a b
  Aligned-reflexivityₗ = Aligned-symmetry Aligned-reflexivityᵣ

  -- Also called: 3.4 in Metamathematische Methoden in der Geometrie.
  Aligned-antisymmetryₗ : (Aligned a b c) → (Aligned b a c) → (a ≡ b)
  Aligned-antisymmetryₗ {a}{b}{c} al-abc al-bac
    with [∃]-intro i ⦃ [∧]-intro al-bib al-aia ⦄ ← Aligned-intersection{a}{b}{c} al-abc al-bac
    with ia ← Aligned-point al-aia
    with ib ← Aligned-point al-bib
    = symmetry(_≡_) ia 🝖 ib

  Aligned-antisymmetryᵣ : (Aligned a b c) → (Aligned a c b) → (b ≡ c)
  Aligned-antisymmetryᵣ al-abc al-acb = symmetry(_≡_) (Aligned-antisymmetryₗ (Aligned-symmetry al-abc) (Aligned-symmetry al-acb))

  -- Also called: 3.6(1) in Metamathematische Methoden in der Geometrie.
  Aligned-transitivityᵣ-exchange : (Aligned a b c) → (Aligned a c d) → (Aligned b c d)
  Aligned-transitivityᵣ-exchange abc acd
    with [∃]-intro i ⦃ [∧]-intro bid cic ⦄ ← Aligned-intersection (Aligned-symmetry abc) (Aligned-symmetry acd)
    with ic ← Aligned-point cic
    = substitute₃-unary₂(Aligned) ic bid

  -- Also called: 3.5(1) in Metamathematische Methoden in der Geometrie.
  Aligned-transitivityₗ-exchange : (Aligned a b d) → (Aligned b c d) → (Aligned a b c)
  Aligned-transitivityₗ-exchange abd bcd = Aligned-symmetry (Aligned-transitivityᵣ-exchange (Aligned-symmetry bcd) (Aligned-symmetry abd))

  -- Also called: 3.7(1) in Metamathematische Methoden in der Geometrie.
  Aligned-semitransitivityᵣ : (Aligned a b c) → (Aligned b c d) → (b ≢ c) → (Aligned a c d)
  Aligned-semitransitivityᵣ {a}{b}{c}{d} abc bcd nbc
    with [∃]-intro x ⦃ [∧]-intro acx cxcd ⦄ ← segment-construction{a}{c}{c}{d}
    with bcx ← Aligned-transitivityᵣ-exchange abc acx
    with xd ← segment-construction-uniqueness nbc ([∧]-intro bcx cxcd) ([∧]-intro bcd (reflexivity(Equidistanced)))
    = substitute₃-unary₃(Aligned) xd acx

  -- Also called: 3.5(2) in Metamathematische Methoden in der Geometrie.
  Aligned-transitivityₗ-merge : (Aligned a b d) → (Aligned b c d) → (Aligned a c d)
  Aligned-transitivityₗ-merge {a}{b}{d}{c} abd bcd with excluded-middle(b ≡ₚ c)
  ... | [∨]-introₗ bc  = substitute₃-unary₂(Aligned) bc abd
  ... | [∨]-introᵣ nbc = Aligned-semitransitivityᵣ (Aligned-transitivityₗ-exchange abd bcd) bcd nbc

  -- Also called: 3.6(2) in Metamathematische Methoden in der Geometrie.
  Aligned-transitivityᵣ-merge : (Aligned a b c) → (Aligned a c d) → (Aligned a b d)
  Aligned-transitivityᵣ-merge abc acd = Aligned-symmetry (Aligned-transitivityₗ-merge (Aligned-symmetry acd) (Aligned-symmetry abc))

  -- Also called: 3.7(2) in Metamathematische Methoden in der Geometrie.
  Aligned-semitransitivityₗ : (Aligned a b c) → (Aligned b c d) → (b ≢ c) → (Aligned a b d)
  Aligned-semitransitivityₗ abc bcd nbc = Aligned-symmetry(Aligned-semitransitivityᵣ (Aligned-symmetry bcd) (Aligned-symmetry abc) (nbc ∘ symmetry(_≡ₚ_)))

  Aligned₄-intro-[123,134] : (Aligned a b c) → (Aligned a c d) → (Aligned₄ a b c d)
  Aligned₄-intro-[123,134] abc acd = abc , abd , acd , bcd where
    abd = Aligned-transitivityᵣ-merge    abc acd
    bcd = Aligned-transitivityᵣ-exchange abc acd

  Aligned₄-intro-[124,234] : (Aligned a b d) → (Aligned b c d) → (Aligned₄ a b c d)
  Aligned₄-intro-[124,234] abd bcd = abc , abd , acd , bcd where
    abc = Aligned-transitivityₗ-exchange abd bcd
    acd = Aligned-transitivityₗ-merge    abd bcd

  -- Existence of two distinct points.
  -- Also called: 3.13 in Metamathematische Methoden in der Geometrie.
  lower-dimension₁ : ∃{Obj = Point ⨯ Point}(\{(a , b) → a ≢ b})
  lower-dimension₁
    with [∃]-intro (a , b , _) ⦃ [∧]-intro ([∧]-intro p _) _ ⦄ ← lower-dimension₂
    = [∃]-intro (a , b) ⦃ ab ↦ p(substitute₃-unary₂(Aligned) ab Aligned-reflexivityₗ) ⦄

  -- Also called: 3.14 in Metamathematische Methoden in der Geometrie.
  extension-existence : ∃(e ↦ (Aligned a b e) ∧ (b ≢ e))
  extension-existence{a}{b}
    with [∃]-intro (x , y) ⦃ nab ⦄ ← lower-dimension₁
    with [∃]-intro e ⦃ [∧]-intro abe bexy ⦄ ← segment-construction{a}{b}{x}{y}
    = [∃]-intro e ⦃ [∧]-intro abe (nab ∘ (be ↦ Equidistanced-point(symmetry(Equidistanced) (substitute₂ₗ(Equidistanced) ([∧]-intro be (reflexivity(_≡ₚ_))) bexy)))) ⦄

  -- Also called: 3.17 in Metamathematische Methoden in der Geometrie.
  triangle-edge-lines-intersection : (Aligned a₁ b₁ c) → (Aligned a₂ b₂ c) → (Aligned a₁ p a₂) → ∃(i ↦ (Aligned p i c) ∧ (Aligned b₁ i b₂))
  triangle-edge-lines-intersection a₁b₁c a₂b₂c a₁pa₂
    with [∃]-intro j ⦃ [∧]-intro pjc b₂ja₁ ⦄ ← Aligned-intersection a₁pa₂ (Aligned-symmetry a₂b₂c)
    with [∃]-intro i ⦃ [∧]-intro b₁ib₂ jic ⦄ ← Aligned-intersection (Aligned-symmetry a₁b₁c) (b₂ja₁)
    = [∃]-intro i ⦃ [∧]-intro (Aligned-transitivityₗ-merge pjc jic) b₁ib₂ ⦄

  -- Also called: 4.6 in Metamathematische Methoden in der Geometrie.
  postulate equidistanced-points-are-aligned : Equidistanced₃(a₁ , b₁ , c₁)(a₂ , b₂ , c₂) → (Aligned a₁ b₁ c₁) → (Aligned a₂ b₂ c₂)

  -- Also called: 5.1 in Metamathematische Methoden in der Geometrie.
  postulate Aligned-order-cases₃-skip₂ : (a ≢ b) → (Aligned a b c₁) → (Aligned a b c₂) → ((Aligned a c₁ c₂) ∨ (Aligned a c₂ c₁))

  -- Also called: 5.2 in Metamathematische Methoden in der Geometrie.
  postulate Aligned-order-cases₃-skip₁ : (a ≢ b) → (Aligned a b c₁) → (Aligned a b c₂) → ((Aligned b c₁ c₂) ∨ (Aligned b c₂ c₁))

  -- Also called: 5.3 in Metamathematische Methoden in der Geometrie.
  postulate Aligned-order-cases₂-skip₃ : (Aligned a b₁ c) → (Aligned a b₂ c) → ((Aligned a b₁ b₂) ∨ (Aligned a b₂ b₁))


  -- The distance between the first pair of points are lesser or equal to the distance between the second pair of points.
  -- The definition states that there should exist a point bₘ such that a (b₁,bₘ) is a subline of (b₁,b₂) and such that the subline is of the same length as (a₁,a₂).
  -- Also called: 5.4 in Metamathematische Methoden in der Geometrie.
  LeDistanced : (Point ⨯ Point) → (Point ⨯ Point) → Stmt
  LeDistanced(a₁ , a₂)(b₁ , b₂) = ∃(bₘ ↦ (Aligned b₁ bₘ b₂) ∧ Equidistanced(a₁ , a₂)(b₁ , bₘ))

  -- Also called: 5.4 in Metamathematische Methoden in der Geometrie.
  GeDistanced : (Point ⨯ Point) → (Point ⨯ Point) → Stmt
  GeDistanced = swap LeDistanced

  -- Also called: 5.5 in Metamathematische Methoden in der Geometrie.
  postulate LeDistanced-alternative : LeDistanced(a₁ , a₂)(b₁ , b₂) ↔ ∃(aₒ ↦ (Aligned a₁ a₂ aₒ) ∧ Equidistanced(a₁ , aₒ)(b₁ , b₂))

  -- Also called: 5.7 in Metamathematische Methoden in der Geometrie.
  instance
    postulate LeDistanced-reflexivity : Reflexivity(LeDistanced)

  -- Also called: 5.8 in Metamathematische Methoden in der Geometrie.
  instance
    postulate LeDistanced-transitivity : Transitivity(LeDistanced)

  -- Also called: 5.9 in Metamathematische Methoden in der Geometrie.
  instance
    postulate LeDistanced-antisymmetry : Antisymmetry(LeDistanced)(Equidistanced)

  -- Also called: 5.10 in Metamathematische Methoden in der Geometrie.
  instance
    postulate LeDistanced-converseTotal : ConverseTotal(LeDistanced)

  -- Also called: 5.11 in Metamathematische Methoden in der Geometrie.
  instance
    postulate LeDistanced-minimal : Weak.Properties.LE.Minimum(LeDistanced)(p , p)

  -- Also called: 5.12 in Metamathematische Methoden in der Geometrie.
  postulate Collinear-aligned-ledistanced-equivalence : (Collinear a b c) → ((Aligned a b c) ↔ (LeDistanced(a , b)(a , c) ∧ LeDistanced(b , c)(a , c)))

  -- Also called: 5.14 in Metamathematische Methoden in der Geometrie.
  LtDistanced : (Point ⨯ Point) → (Point ⨯ Point) → Stmt
  LtDistanced(a₁ , a₂)(b₁ , b₂) = LeDistanced(a₁ , a₂)(b₁ , b₂) ∧ (¬ Equidistanced(a₁ , a₂)(b₁ , b₂))

  -- Also called: 5.14 in Metamathematische Methoden in der Geometrie.
  GtDistanced : (Point ⨯ Point) → (Point ⨯ Point) → Stmt
  GtDistanced = swap GeDistanced



  aligned-equidistanced-equality : (Aligned a b₁ b₂) → Equidistanced(a , b₁)(a , b₂) → (b₁ ≡ₚ b₂)
  aligned-equidistanced-equality ab₁b₂ ab₁ab₂ = {!!}

  aligned-equidistanced-last-equality : (a ≢ b) → (Aligned a b c₁) → (Aligned a b c₂) → Equidistanced(b , c₁)(b , c₂) → (c₁ ≡ c₂)
  aligned-equidistanced-last-equality nab abc₁ abc₂ bc₁bc₂ = {!Aligned-order-cases₃-skip₁ nab abc₁ abc₂!}

  Aligned-classical : Classical₃(Aligned)
  Classical.excluded-middle (Aligned-classical {a} {b} {c})
    with [∃]-intro d ⦃ [∧]-intro abd bdbc ⦄ ← segment-construction{a}{b}{b}{c}
    with excluded-middle(a ≡ₚ b) | excluded-middle(c ≡ₚ d)
  ... | _              | [∨]-introₗ cd  = [∨]-introₗ (substitute₃-unary₃(Aligned) (symmetry(_≡ₚ_) cd) abd)
  ... | [∨]-introₗ ab  | [∨]-introᵣ ncd = [∨]-introₗ (substitute₃-unary₂(Aligned) ab Aligned-reflexivityₗ)
  ... | [∨]-introᵣ nab | [∨]-introᵣ ncd = [∨]-introᵣ (abc ↦ ncd(aligned-equidistanced-last-equality nab abc abd (symmetry(Equidistanced) bdbc)))


  {-
  -- Also called: 6.14 in Metamathematische Methoden in der Geometrie.
  lineSet : (a : Point) → (b : Point) → ⦃ distinct : (a ≢ b) ⦄ → PredSet(Point)
  lineSet a b ∋ p = Collinear a p b
  PredSet.preserve-equiv (lineSet a b) = {!TrinaryRelator.unary₂(Collinear)!} -- TODO-}

  -- Example:
  --         (c)
  --       /     \
  --    (m₁)\   /(m₂)
  --    /   _(i)_   \
  --  (a)__/     \__(b)
  -- Also called: Outer Pasch.
  postulate Aligned-outer-intersection : (Aligned a i m₂) → (Aligned b m₂ c) → ∃(m₁ ↦ (Aligned a m₁ c) ∧ (Aligned b i m₁))
  {-Aligned-outer-intersection {a}{i}{m₂}{b}{c} aim2 bm2c with excluded-middle(Collinear b i m₂) ⦃ classical ⦄
  Aligned-outer-intersection {a}{i}{m₂}{b}{c} aim2 bm2c | [∨]-introₗ coll-bim2 with excluded-middle(Aligned b i m₂) ⦃ classical ⦄
  ... | [∨]-introₗ al-bim2 = [∃]-intro c ⦃ [∧]-intro {!!} ([∨]-elim ([∨]-elim (al-bim2 ↦ {!!}) (al-im2b ↦ {!!})) (al-m2bi ↦ {!!}) coll-bim2) ⦄
  ... | [∨]-introᵣ x = {!!}
  Aligned-outer-intersection {a}{i}{m₂}{b}{c} aim2 bm2c | [∨]-introᵣ x = {!!}-}
    {-with [∃]-intro ii ⦃ p ⦄ ← Aligned-intersection {!!} {!!}
    = {!!}-}

{-


  -- A point on the bisecting ray of the given line.
  -- Example:
  --        ⋮
  --        |
  --       (p)
  --      / | \
  --     /  |  \
  --   (a)-----(b)
  --        |
  --        ⋮
  BisectingRayPoint : Point → Point → Point → Stmt
  BisectingRayPoint a p b = Equidistanced(a , p)(b , p)

  -- The points are all aligned in a line with the second point being in the center of the line constructed from the other points.
  -- Example:
  --   (a)---(m)---(b)
  -- `m` is the centerpoint (in the middle) of `a` and `b`.
  CenterAligned : Point → Point → Point → Stmt
  CenterAligned a m b = (BisectingRayPoint a m b) ∧ (Aligned a m b)

  -- The points form a perpendicular triangle with b being the corner where the perpendicular angle is residing.
  -- Example:
  --       (a)
  --      / | \
  --     /  |  \
  --    /   |   \
  --  (c)--(b)--(cₘ)
  PerpendicularCorner : Point → Point → Point → Stmt
  PerpendicularCorner a b c = ∃(cₘ ↦ (CenterAligned c b cₘ) ∧ (BisectingRayPoint c a cₘ))

  -- The distance between the first pair of points are lesser or equal to the distance between the second pair of points.
  -- This is defined by considering points on a bisecting ray in the center of each of the two lines constructed from the pairs of points. If there is a function that maps points on the second bisecting ray to the first bisecting ray such that this mapping preserves the distance to one of the endpoints of its corresponding line, then the distance between the first pair is lesser than the second.
  -- Example:
  --    (bBisect)
  --       /|\
  --      / | \
  --     /  |  \
  --  (b₁)=====(b₂)

  --   (aBisect)
  --      /|\
  --     / | \
  --    |  |  |
  --  (a₁)===(a₂)
  --
  --   Here, b₁ and b₂ are equally distanced to bBisect.
  --   The definition then states that there exists a similiar construction aBisect on a₁ and a₂, and it does.
  --   And this second construction (aBisect) should have the same distance to its endpoints (for example a₂) as the first (bBisect) have (for example b₂), which it does.
  --   Now, in the extreme case where the distance between bBisect and the endpoints are shrunk, bBisect would collapse into being a center point of the line (b₁,b₂), but because the distance between a₁ and a₂ is smaller, aBisect will still be outside of the line (a₁,a₂). Though, it still exists.
  --   This would not be the case if the relation was reversed.
  LeDistanced2 : (Point ⨯ Point) → (Point ⨯ Point) → Stmt
  LeDistanced2(a₁ , a₂)(b₁ , b₂) =
    ∀{bBisect} → (BisectingRayPoint b₁ bBisect b₂) →
    ∃(aBisect  ↦ (BisectingRayPoint a₁ aBisect a₂) ∧ Equidistanced(a₂ , aBisect)(b₂ , bBisect))

  -- Aligned-Distanced-equivalence : (Aligned a b c) ↔ (∀{d} → LeDistanced2(a , d)(a , b) → LeDistanced2(c , d)(b , c) → (b ≡ d))

  -- Note: The only purpose of this definition is so that instance search works (because it do not work on functions, and negation is defined as a function).
  record DistinctPoints (a b : Point) : Type{ℓₚₑ} where
    constructor intro
    field proof : (a ≢ b)

  -- A line segment is a geometric figure defined by two distinct points
  -- The interpretation is that these two points connect each other, and the set of points of the figure are the points between these two points.
  record LineSegment : Type{ℓₚ Lvl.⊔ ℓₚₑ} where
    constructor lineSegment
    field
      from : Point
      to : Point
      ⦃ distinct ⦄ : DistinctPoints from to

    -- A point on the line segment.
    point : Point
    point = [∃]-witness (Aligned-intersection {to}{from} {from} {to}{from} Aligned-reflexivityᵣ Aligned-reflexivityᵣ)

    -- The line segment flipped.
    flip : LineSegment
    flip = record{from = to ; to = from ; distinct = intro(DistinctPoints.proof distinct ∘ symmetry(_≡_))}

    copyTo : Point → LineSegment
    copyTo base = {!!}

    -- TODO: This is apparently difficult to construct
    center : Point
    -- center = {!!}

    -- The bisector (TODO: which one?) line of this line segment. (TODO: Too unspecific. Where does it start and end?)
    bisector : LineSegment
    -- bisector = {!!}
  private variable l l₁ l₂ l₃ : LineSegment

  -- Point inclusion in line segment (a point is in a line segment).
  _∈₂_ : Point → LineSegment → Type
  p ∈₂ lineSegment a b = Aligned a p b

  -- Line segment congruence (two line segments are of equal length)
  _⎶_ : LineSegment → LineSegment → Type
  lineSegment a₁ a₂ ⎶ lineSegment b₁ b₂ = Equidistanced(a₁ , a₂)(b₁ , b₂)

  Perpendicular : LineSegment → LineSegment → Stmt
  Perpendicular(lineSegment a₁ a₂)(lineSegment b₁ b₂) = ∃(c ↦ (Collinear a₁ a₂ c) ∧ (Collinear b₁ b₂ c) ∧ (PerpendicularCorner a₂ c b₂))

  Parallel : LineSegment → LineSegment → Stmt
  Parallel a b = Perpendicular a (LineSegment.bisector b)

  point-in-lineSegment : LineSegment.point(l) ∈₂ l
  point-in-lineSegment{l} = [∧]-elimₗ([∃]-proof (Aligned-intersection Aligned-reflexivityᵣ Aligned-reflexivityᵣ))

  -- A triangle is a geometric figure defined by three unaligned points.
  -- The interpretation is that these three points connect each other, forming three line segments, and the set of points of the figure are the points inside the line segments.
  record Triangle : Type{ℓₚ Lvl.⊔ ℓₗᵢₗ} where
    constructor triangle
    field
      point₁ : Point
      point₂ : Point
      point₃ : Point
      ⦃ distinct₁ ⦄ : ¬ Aligned point₁ point₂ point₃
      ⦃ distinct₂ ⦄ : ¬ Aligned point₂ point₃ point₁
      ⦃ distinct₃ ⦄ : ¬ Aligned point₃ point₁ point₂

    side₁₂ : LineSegment
    side₁₂ = line point₁ point₂ ⦃ intro(contrapositiveᵣ (p1p2 ↦ substitute₃-unary₁(Aligned) (symmetry(_≡_) p1p2) Aligned-reflexivityₗ) distinct₁) ⦄

    side₂₃ : LineSegment
    side₂₃ = line point₂ point₃ ⦃ intro(contrapositiveᵣ (p2p3 ↦ substitute₃-unary₁(Aligned) (symmetry(_≡_) p2p3) Aligned-reflexivityₗ) distinct₂) ⦄

    side₃₁ : LineSegment
    side₃₁ = line point₃ point₁ ⦃ intro(contrapositiveᵣ (p3p1 ↦ substitute₃-unary₁(Aligned) (symmetry(_≡_) p3p1) Aligned-reflexivityₗ) distinct₃) ⦄
  private variable tri tri₁ tri₂ : Triangle

  -- A triangle exists.
  -- This comes directly from an axiom.
  Triangle-existence : Triangle
  Triangle-existence
    with [∃]-intro(x , y , z) ⦃ [∧]-intro ([∧]-intro p q) r ⦄ ← lower-dimension
    = triangle x y z ⦃ p ⦄ ⦃ q ⦄ ⦃ r ⦄

  Aligned-four : (Aligned a b c) → (Aligned p₁ b c) → (Aligned a b p₂) → (Aligned p₁ b p₂)
  Aligned-four abc p₁bc abp₂
    with [∃]-intro d ⦃ [∧]-intro bdp₂ bdc ⦄ ← Aligned-intersection (Aligned-symmetry abc) (Aligned-symmetry abp₂)
    with [∃]-intro e ⦃ [∧]-intro bep₁ bea ⦄ ← Aligned-intersection abc p₁bc
    = {!Aligned-transitivityᵣ abp₂ p₁bc!}
  Aligned-alternative-start : (Aligned a₁ b c)→ (Aligned a₂ b c) → ((Aligned a₁ a₂ b) ∨ (Aligned a₂ a₁ b))

  -- Note: The difference between segment-construction and this is that this is not extending the line (a₁,b₁). segment-equidistanced-copy constructs a new line which is of the same length as (a₂,b₂) but starting from a₁ and is in the direction of p.
  -- TODO: A proof idea is to use center-of-3 and eliminate the last case. For the different cases, one uses different segment-constructions as usual
  segment-equidistanced-copy : ∃(p ↦ ((Aligned a₁ b₁ p) ∨ (Aligned a₁ p b₁)) ∧ Equidistanced(a₁ , p)(a₂ , b₂))
  segment-equidistanced-copy {a₁}{b₁} {a₂}{b₂}
    with [∃]-intro ext ⦃ [∧]-intro al-b₁a₁ext d-a₁ext-a₂b₂ ⦄ ← segment-construction{b₁}{a₁} {a₂}{b₂}
    with [∃]-intro p   ⦃ [∧]-intro al-exta₁p  d-a₁p-exta₁  ⦄ ← segment-construction{ext}{a₁} {ext}{a₁}
    with center-of-3 {a₁}{b₁}{p}
  ... | [∨]-introₗ ([∨]-introₗ ([∨]-introₗ al-a₁b₁p)) = [∃]-intro p ⦃ [∧]-intro ([∨]-introₗ al-a₁b₁p) (d-a₁p-exta₁ 🝖 Equidistanced-flipped 🝖 d-a₁ext-a₂b₂) ⦄
  ... | [∨]-introₗ ([∨]-introₗ ([∨]-introᵣ al-b₁pa₁)) = [∃]-intro p ⦃ [∧]-intro ([∨]-introᵣ (Aligned-symmetry al-b₁pa₁)) (d-a₁p-exta₁ 🝖 Equidistanced-flipped 🝖 d-a₁ext-a₂b₂) ⦄
  ... | [∨]-introₗ ([∨]-introᵣ             al-pa₁b₁)  = [∃]-intro p ⦃ [∧]-intro ([∨]-introᵣ {!!}) (d-a₁p-exta₁ 🝖 Equidistanced-flipped 🝖 d-a₁ext-a₂b₂) ⦄ -- TODO: Use Aligned-four to prove (a₁ ≡ ext), which implies (a₁ ≡ p), so therefore ( Aligned a₁ a₁ b₁) by substitution. Note that this is the case when (a₂ ≡ b₂), but it is not used in the proof.
  ... | [∨]-introᵣ x = {!!} -- TODO: x essentially states that a₁ b₁ p is not in a line, which can be proven that they are like in the cases above by Aligned-alternative-start

  -- A circle is a geometric figure defined by two distinct points.
  -- The interpretation is that the first point is the center point, and the second point lies on the arc of the circle.
  -- The distance between the points is the radius of the circle, and all points within the radius from the center point defines the set of points of the circle.
  record Circle : Type{ℓₚ Lvl.⊔ ℓₚₑ} where
    constructor circle
    field
      center : Point
      outer : Point
      ⦃ distinct ⦄ : DistinctPoints center outer

    -- A line from the center point to the arc.
    radiusLineSegment : LineSegment
    radiusLineSegment = lineSegment center outer

    {- TODO
    -- A line from the center point to the arc in the direction of the given point.
    radiusLineSegmentTowards : Point → LineSegment
    radiusLineSegmentTowards p
      with [∃]-intro q ⦃ [∧]-intro cpq pqco ⦄ ← segment-construction{center}{p} {center}{outer}
      = lineSegment center q ⦃ intro(cq ↦ (
        • (
          • center ≡ q                          :-[ cq ]
          • Aligned center p q                  :-[ cpq ]
          ⇒₂-[ substitute₃-unary₁(Aligned) ]
          Aligned q p q                         ⇒-[ Aligned-point ]
          p ≡ q                                 ⇒-[ pq ↦ [∧]-intro pq (reflexivity(_≡_)) ]
          (p ≡ q) ∧ (q ≡ q)                     ⇒-end
        )
        • Equidistanced(p , q) (center , outer) :-[ pqco ]
        ⇒₂-[ substitute₂ₗ(Equidistanced) ]
        Equidistanced(q , q) (center , outer)   ⇒-[ symmetry(Equidistanced) ]
        Equidistanced(center , outer) (q , q)   ⇒-[ Equidistanced-point ]
        center ≡ outer                          ⇒-[ DistinctPoints.proof distinct ]
        ⊥                                       ⇒-end
      )) ⦄

    -- TODO: I am confused. Is the point (LineSegment.to(radiusLineTowards p)) always further away than p?
    radiusLineTowards-aligned : Aligned center p (Line.to(radiusLineSegmentTowards p))
    radiusLineTowards-aligned{p}
      with [∃]-intro q ⦃ [∧]-intro cpq pqco ⦄ ← segment-construction{center}{p} {center}{outer}
      = cpq

    radiusLineSegmentTowards-radius : Equidistanced(center , LineSegment.to(radiusLineSegmentTowards p)) (center , outer)
    radiusLineSegmentTowards-radius{p}
      with [∃]-intro q ⦃ [∧]-intro cpq pqco ⦄ ← segment-construction{center}{p} {center}{outer}
      = {!pqco!} -- TODO: pqco is actually stating that (p,q) and (center,outer) is equally distanced, which is not what we want, so radiusLineTowards should be modified to use segment-construction-alt
    -}

    -- TODO: Two circles' intersection points are either 0, 1, 2 or they are the same circle.
    -- intersection : ∀{C₁ C₂} → (∀{p} → ¬(p ∈ₒ C₁) ∧ ¬(p ∈ₒ C₂)) ∨ ∃!(p ↦ (p ∈ₒ C₁) ∧ (p ∈ₒ C₂)) ∨ ∃(p₁ ↦ ∃(p₂ ↦ (p ∈ₒ C₁) ∧ (p ∈ₒ C₂))) ∨ (C₁ ≡ C₂)

  -- Point inclusion in circle (a point is in a circle).
  _∈ₒ_ : Point → Circle → Type
  p ∈ₒ circle c o = LeDistanced(c , p)(c , o)
  -- TODO: Is this equivalent? ∃(op ↦ Equidistanced(c , o)(c , op) ∧ (Aligned c p op)) It extends the line (c,p) instead of shrinking the line (c,o)
-}
