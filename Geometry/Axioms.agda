open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Logic
import      Lvl
open import Type
open import Structure.Setoid.WithLvl

-- An axiomatic approach to plane geometry.
-- The axiomatic system used are called "Tarski's axioms", and plane geometry is also known as two-dimensional Euclidean geometry.
module Geometry.Axioms
  {ℓₚ ℓₚₑ ℓₗₗₑ ℓₗᵢₗ}
  (Point : Type{ℓₚ}) ⦃ Point-equiv : Equiv{ℓₚₑ}(Point) ⦄
  (Equidistanced : (Point ⨯ Point) → (Point ⨯ Point) → Stmt{ℓₗₗₑ}) -- Two pairs of points have the same distance between each other.
  (Aligned : Point → Point → Point → Stmt{ℓₗᵢₗ})                   -- Three points are aligned in order. The second point is between the first and the third.
  where

open import Data.Tuple.Equiv
open import Functional
open import Logic.Predicate
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Relator
open import Syntax.Function
open import Syntax.Implication
open import Syntax.Transitivity
open import Syntax.Type

private variable ℓ ℓ₁ ℓ₂ ℓₗ ℓₗ₁ ℓₗ₂ : Lvl.Level
private variable p a b c d e p₁ p₂ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂ m₁ m₂ : Point
private variable P Q : Point → Stmt{ℓ}

-- Source: Tarski's axioms of geometry (https://en.wikipedia.org/wiki/Tarski%27s_axioms @ 2020-06-14).
-- TODO: Are there any modifications of the axioms when working in constructive logic?
record Axioms : Typeω where
  field
    ⦃ Equidistanced-relator ⦄ : BinaryRelator(Equidistanced)
    ⦃ Aligned-relator ⦄ : TrinaryRelator(Aligned)

    -- The distance between p₁ and p₂ is the same as the distance between p₂ and p₁.
    -- The order of the points in the equidistance relation does not matter.
    -- Example:
    --   • (p₁) <--- (p₂)
    --   • (p₁) ---> (p₂)
    --   These two drawings depict lines between points p₁ and p₂. They have the same length.
    --   So there is no need to draw an arrow head on the lines when referring to the length of a line.
    Equidistanced-flipped : Equidistanced(p₁ , p₂)(p₂ , p₁)

    -- Equidistance is a transitive relation.
    -- Example:
    --   la: (a₁) ---- (a₂)
    --   lb: (b₁) ---- (b₂)
    --   lc: (c₁) ---- (c₂)
    --   Here is a drawing of three lines.
    --   The line la have the same length as lb, and the line la have the same length as lc. Then lb have the same length as lc.
    Equidistanced-symmetric-transitivity : Equidistanced(a₁ , a₂)(b₁ , b₂) → Equidistanced(a₁ , a₂)(c₁ , c₂) → Equidistanced(b₁ , b₂)(c₁ , c₂)

    -- If two points have the same distance as the distance between a single point with itself, then they are the same point.
    -- Essentially, if two points have no distance between each other, they are the same point.
    -- Example:
    --   (p₁) ---------- (p₂)
    --   (p)
    --   Here p₁ and p₂ are arbitrary points, and a line between them is depicted.
    --   The line from p to p is also depicted (as a point).
    --   Currently, these lines do not have the same length, and for p₁ and p₂ to have the same distance as the single point line consisting of p, the line must collapse to a single point, making p₁ and p₂ the same point.
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
    segment-construction : ∃(b₁ ↦ (Aligned a₁ p b₁) ∧ Equidistanced(p , b₁)(a₂ , b₂))

    five-segment : (a₁ ≢ b₁) → (Aligned a₁ b₁ c₁) → (Aligned a₂ b₂ c₂) → Equidistanced(a₁ , b₁)(a₂ , b₂) → Equidistanced(b₁ , c₁)(b₂ , c₂) → Equidistanced(a₁ , d₁)(a₂ , d₂) → Equidistanced(b₁ , e₁)(b₂ , e₂) → Equidistanced(c₁ , e₁)(c₂ , e₂)

    -- If a point is between two identical points, then they are the same point.
    -- Alternatively, if a point is in a line consisting of only a single point, then the point is the single point.
    -- Example:
    --   (p₁) ------(a)--- (p₂)
    --   Here, a line from p₁ to p₂ is depicted, and a point a is in this line.
    --   But if p₁ and p₂ would be the same point p, then the line would collapse to a single point, making a and p the same.
    Aligned-point : Aligned p a p → (a ≡ p)

    -- Given two connected lines and one point in each of the lines, two lines connecting the points and the endpoints of the other line have an intersection point.
    -- Example:
    --         (c)
    --       /     \
    --    (m₁)\   /(m₂)
    --    /   _(i)_   \
    --  (a)__/     \__(b)
    Aligned-intersection : (Aligned a m₁ c) → (Aligned b m₂ c) → ∃(i ↦ (Aligned m₁ i b) ∧ (Aligned m₂ i a))

    Aligned-continuity : ∃(a ↦ ∀{x y} → P(x) → Q(y) → (Aligned a x y)) → ∃(a ↦ ∀{x y} → P(x) → Q(y) → (Aligned x a y))

    -- A triangle exists.
    -- This excludes the possibility of this theory describing 0 or 1-dimensional spaces when using the standard interpretation of the axioms.
    -- Example:
    --    (c)
    --   /   \
    -- (a)___(b)
    lower-dimension : ∃{Obj = Point ⨯ Point ⨯ Point}(\(a , b , c) → (¬ Aligned a b c) ∧ (¬ Aligned b c a) ∧ (¬ Aligned c a b))

    upper-dimension : Equidistanced(a , p₁)(a , p₂) → Equidistanced(b , p₁)(b , p₂) → Equidistanced(c , p₁)(c , p₂) → (p₁ ≢ p₂) → (Aligned a b c) ∨ (Aligned b c a) ∨ (Aligned c a b)

    -- Given three points, they either form a line, or there is a center point between the three points.
    -- Example:
    --   Here is an example of the different cases depicted:
    --   • (a) ----(b)------ (c)
    --   • (b) ----(c)------ (a)
    --   • (c) ----(a)------ (b)
    --   •     (a)\__
    --        /      \__
    --      /    (m)     \
    --    (b)_____________(c)
    center-of-3 : (Aligned a b c) ∨ (Aligned b c a) ∨ (Aligned c a b) ∨ ∃(m ↦ Equidistanced(a , m)(b , m) ∧ Equidistanced(a , m)(c , m))

module _ ⦃ axioms : Axioms ⦄ where
  open Axioms(axioms)

  instance
    -- Identical pairs of points have the same distance between each other.
    Equidistanced-reflexivity : Reflexivity(Equidistanced)
    Reflexivity.proof Equidistanced-reflexivity {p₁ , p₂} = Equidistanced-symmetric-transitivity (Equidistanced-flipped {p₂}{p₁}) (Equidistanced-flipped {p₂}{p₁})

  instance
    Equidistanced-symmetry : Symmetry(Equidistanced)
    Symmetry.proof Equidistanced-symmetry p = Equidistanced-symmetric-transitivity p (reflexivity(Equidistanced))

  instance
    Equidistanced-transitivity : Transitivity(Equidistanced)
    Transitivity.proof Equidistanced-transitivity p q = Equidistanced-symmetric-transitivity (symmetry(Equidistanced) p) q

  instance
    Equidistanced-equivalence : Equivalence(Equidistanced)
    Equidistanced-equivalence = intro

  -- The distance between a point and itself is the same for all points.
  Equidistanced-points : Equidistanced(a , a) (b , b)
  Equidistanced-points {a}{b}
    with [∃]-intro p ⦃ [∧]-intro _ equi ⦄ ← segment-construction{a}{b} {a}{a}
    =
      • (b ≡ b) ∧ (p ≡ b)            :-[ [∧]-intro (reflexivity(_≡_)) (symmetry(_≡_) (Equidistanced-point equi)) ]
      • Equidistanced(b , p) (b , p) :-[ reflexivity(Equidistanced) ]
      ⇒₂-[ substitute₂ᵣ(Equidistanced) ]
      Equidistanced(b , p) (b , b) ⇒-[ Equidistanced-symmetric-transitivity equi ]
      Equidistanced(a , a) (b , b) ⇒-end

  -- Two points are always aligned.
  Aligned-reflexivityᵣ : Aligned a b b
  Aligned-reflexivityᵣ {a}{b}
    with [∃]-intro p ⦃ [∧]-intro alig equi ⦄ ← segment-construction{a}{b} {a}{a}
    = substitute₃-unary₃(Aligned) (symmetry(_≡_) (Equidistanced-point equi)) alig

  -- A single point is always aligned with itself.
  Aligned-reflexivity : Aligned a a a
  Aligned-reflexivity = Aligned-reflexivityᵣ

  -- When three points are aligned in one direction, they are also aligned in the opposite direction.
  Aligned-symmetry : Aligned a b c → Aligned c b a
  Aligned-symmetry {a}{b}{c} alig
    with [∃]-intro p ⦃ [∧]-intro bpb cpa ⦄ ← Aligned-intersection{a}{b}{_}{b}{c} alig Aligned-reflexivityᵣ
    with pb ← Aligned-point bpb
    = substitute₃-unary₂(Aligned) pb cpa

  -- Two points are always aligned.
  Aligned-reflexivityₗ : Aligned a a b
  Aligned-reflexivityₗ = Aligned-symmetry Aligned-reflexivityᵣ

  Aligned-transitivityᵣ-exchange : (Aligned a b c) → (Aligned a c d) → (Aligned b c d)
  Aligned-transitivityᵣ-exchange abc acd
    with [∃]-intro i ⦃ [∧]-intro bid cic ⦄ ← Aligned-intersection (Aligned-symmetry abc) (Aligned-symmetry acd)
    with ic ← Aligned-point cic
    = substitute₃-unary₂(Aligned) ic bid

  Aligned-transitivityₗ-exchange : (Aligned a b d) → (Aligned b c d) → (Aligned a b c)
  Aligned-transitivityₗ-exchange abd bcd = Aligned-symmetry (Aligned-transitivityᵣ-exchange (Aligned-symmetry bcd) (Aligned-symmetry abd))

  Aligned-antisymmetryₗ : (Aligned a b c) → (Aligned b a c) → (a ≡ b)
  Aligned-antisymmetryₗ {a}{b}{c} al-abc al-bac
    with [∃]-intro i ⦃ [∧]-intro al-bib al-aia ⦄ ← Aligned-intersection{a}{b}{c} al-abc al-bac
    with ia ← Aligned-point al-aia
    with ib ← Aligned-point al-bib
    = symmetry(_≡_) ia 🝖 ib

  Aligned-antisymmetryᵣ : (Aligned a b c) → (Aligned a c b) → (b ≡ c)
  Aligned-antisymmetryᵣ al-abc al-acb = symmetry(_≡_) (Aligned-antisymmetryₗ (Aligned-symmetry al-abc) (Aligned-symmetry al-acb))

  Collinear : Point → Point → Point → Stmt
  Collinear a b c = (Aligned a b c) ∨ (Aligned b c a) ∨ (Aligned c a b)

  -- Note: The only purpose of this definition is so that instance search works (because it do not work on functions, and negation is defined as a function).
  record DistinctPoints (a b : Point) : Type{ℓₚₑ} where
    constructor intro
    field proof : (a ≢ b)

  -- A line is a geometric figure defined by two distinct points
  -- The interpretation is that these two points connect each other, and the set of points of the figure are the points between these two points.
  record Line : Type{ℓₚ Lvl.⊔ ℓₚₑ} where
    constructor line
    field
      from : Point
      to : Point
      ⦃ distinct ⦄ : DistinctPoints from to

    flip : Line
    flip = record{from = to ; to = from ; distinct = intro(DistinctPoints.proof distinct ∘ symmetry(_≡_))}
  private variable l l₁ l₂ l₃ : Line

  -- Point inclusion in line (a point is in a line).
  _∈₂_ : Point → Line → Type
  p ∈₂ line a b = Aligned a p b

  -- Line congruence (two lines are of equal length)
  _⎶_ : Line → Line → Type
  line a₁ a₂ ⎶ line b₁ b₂ = Equidistanced(a₁ , a₂)(b₁ , b₂)

  -- A triangle is a geometric figure defined by three unaligned points.
  -- The interpretation is that these three points connect each other, forming three lines, and the set of points of the figure are the points inside the lines.
  record Triangle : Type{ℓₚ Lvl.⊔ ℓₗᵢₗ} where
    constructor triangle
    field
      point₁ : Point
      point₂ : Point
      point₃ : Point
      ⦃ distinct₁ ⦄ : ¬ Aligned point₁ point₂ point₃
      ⦃ distinct₂ ⦄ : ¬ Aligned point₂ point₃ point₁
      ⦃ distinct₃ ⦄ : ¬ Aligned point₃ point₁ point₂

    side₁₂ : Line
    side₁₂ = line point₁ point₂ ⦃ intro(contrapositiveᵣ (p1p2 ↦ substitute₃-unary₁(Aligned) (symmetry(_≡_) p1p2) Aligned-reflexivityₗ) distinct₁) ⦄

    side₂₃ : Line
    side₂₃ = line point₂ point₃ ⦃ intro(contrapositiveᵣ (p2p3 ↦ substitute₃-unary₁(Aligned) (symmetry(_≡_) p2p3) Aligned-reflexivityₗ) distinct₂) ⦄

    side₃₁ : Line
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
    radiusLine : Line
    radiusLine = line center outer

    {- TODO
    -- A line from the center point to the arc in the direction of the given point.
    radiusLineTowards : Point → Line
    radiusLineTowards p
      with [∃]-intro q ⦃ [∧]-intro cpq pqco ⦄ ← segment-construction{center}{p} {center}{outer}
      = line center q ⦃ intro(cq ↦ (
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

    -- TODO: I am confused. Is the point (Line.to(radiusLineTowards p)) always further away than p?
    radiusLineTowards-aligned : Aligned center p (Line.to(radiusLineTowards p))
    radiusLineTowards-aligned{p}
      with [∃]-intro q ⦃ [∧]-intro cpq pqco ⦄ ← segment-construction{center}{p} {center}{outer}
      = cpq

    radiusLineTowards-radius : Equidistanced(center , Line.to(radiusLineTowards p)) (center , outer)
    radiusLineTowards-radius{p}
      with [∃]-intro q ⦃ [∧]-intro cpq pqco ⦄ ← segment-construction{center}{p} {center}{outer}
      = {!pqco!} -- TODO: pqco is actually stating that (p,q) and (center,outer) is equally distanced, which is not what we want, so radiusLineTowards should be modified to use segment-construction-alt
    -}

  -- Point inclusion in circle (a point is in a circle).
  _∈ₒ_ : Point → Circle → Type
  p ∈ₒ circle c o = ∃(os ↦ Equidistanced(c , o)(c , os) ∧ (Aligned c p os))
