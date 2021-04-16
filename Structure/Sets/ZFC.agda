open import Type
open import Structure.Relator
open import Structure.Setoid renaming (_≡_ to _≡ₑ_)

module Structure.Sets.ZFC {ℓₛ ℓₗ ℓₑ} {S : Type{ℓₛ}} ⦃ equiv : Equiv{ℓₑ}(S) ⦄ (_∈_ : S → S → Type{ℓₗ}) ⦃ [∈]-binaryRelator : BinaryRelator(_∈_) ⦄ where

open import Functional
open import Function.Equals
import      Lvl
open import Logic.Predicate
open import Logic.Propositional
open import Type.Properties.Inhabited
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Proofs renaming ([≡]-binaryRelator to [≡ₑ]-binaryRelator)
open import Structure.Setoid.Uniqueness
import      Structure.Sets.Names
open import Syntax.Function
open import Syntax.Implication

private variable ℓ ℓ₁ ℓ₂ ℓₑ₁ : Lvl.Level
private variable A B C D E a b c d e x y z As : S
private variable f g h : S → S
private variable P Q R : S → Type{ℓ}
private variable ⦃ func ⦄ : Function ⦃ equiv ⦄ ⦃ equiv ⦄ (f)
private variable ⦃ unaryRel ⦄ : UnaryRelator ⦃ equiv ⦄ (P)

open        Structure.Sets.Names.From-[∈] (_∈_)
open        Structure.Sets.Names.Relations (_∈_)
open        Structure.Sets.Names.One                     (_∈_)
open        Structure.Sets.Names.Two                     (_∈_)(_∈_)
open        Structure.Sets.Names.TwoDifferent            (_∈_)(_∈_)
open        Structure.Sets.Names.TwoSame                 (_∈_)(_∈_)
open        Structure.Sets.Names.Three                   (_∈_)(_∈_)(_∈_)
open        Structure.Sets.Names.ThreeNestedTwoDifferent (_∈_)
open        Structure.Sets.Names.ThreeTwoNested          (_∈_)(_∈_)(_∈_)
open import Structure.Sets.Quantifiers(_∈_)
open import Structure.Sets.Quantifiers.Proofs(_∈_) ⦃ [∈]-binaryRelator ⦄

{-
-- The statement that the sets in ss are all pairwise disjoint
PairwiseDisjoint : S → Type
PairwiseDisjoint(ss) = ∀ₛ(ss)(s₁ ↦ ∀ₛ(ss)(s₂ ↦ ∀ₗ(x ↦ ((x ∈ s₁) → (x ∈ s₂) → (s₁ ≡ s₂)))))
-- ∀ₛ(ss)(s₁ ↦ ∀ₛ(ss)(s₂ ↦ (s₁ ≢ s₂) → Disjoint(s₁)(s₂)))

-- The statement that the relation predicate F can be interpreted as a partial function
PartialFunction : (S → S → Type{ℓ}) → S → Type
PartialFunction(F) (dom) = ∀ₛ(dom)(x ↦ Unique(y ↦ F(x)(y)))

-- The statement that the relation predicate F can be interpreted as a total function
TotalFunction : (S → S → Type{ℓ}) → S → Type
TotalFunction(F) (dom) = ∀ₛ(dom)(x ↦ ∃!(y ↦ F(x)(y)))

-- A binary relator modifier which makes the binary relator to a statement about all distinct pairs in a set.
-- Note: This is specifically for irreflexive binary relations.
DistinctivelyPairwise : (S → S → Type{ℓ}) → (S → Type)
DistinctivelyPairwise Related (S) = ∀ₛ(S)(a ↦ ∀ₛ(S)(b ↦ ((a ≢ b) → Related(a)(b))))
-}

record ZFC : Typeω where
  field
    -- Empty set
    -- The set consisting of no elements.
    ∅ : S

    -- Pair set.
    -- The set consisting of only two elements.
    pair : S → S → S

    -- Subset filtering.
    -- The subset of the specified set where all elements satisfy the specified formula.
    filter : (P : S → Type{ℓ}) ⦃ rel-P : UnaryRelator(P) ⦄ → (S → S)

    -- Union over arbitrary sets.
    -- Constructs a set which consists of elements which are in any of the specified sets.
    ⋃ : S → S

    -- Power set.
    -- The set of all subsets of the specified set.
    ℘ : S → S

    -- The map of a set.
    -- The set of values when a function is applied to every element of a set.
    -- Or: The image of the function on the set.
    -- Or: The image of the function.
    map : (f : S → S) ⦃ func-f : Function(f) ⦄ → (S → S)

    -- The set of all finite ordinals.
    -- A set which has the `Inductive`-property. Also infinite.
    ω₀ : S

    -- A choice function for non-empty sets in a family of sets.
    -- Chooses an arbitrary element in a non-empty set from a family of sets.
    -- Example: choose {ℕ,ℤ,ℚ,ℝ} ℝ ∈ ℝ.
    choose : S → S → S

  -- Singleton set.
  -- A set consisting of only a single element.
  singleton : S → S
  singleton(s) = pair(s)(s)

  -- Union operator.
  -- Constructs a set which consists of both elements from LHS and RHS.
  _∪_ : S → S → S
  a ∪ b = ⋃(pair a b)
  infixl 3000 _∪_

  -- The zero constant expressed in the standard inductive set definition of ℕ in ZFC set theory.
  𝟎 : S
  𝟎 = ∅

  -- The successor function expressed in the standard inductive set definition of ℕ in ZFC set theory.
  -- This definition implies that natural numbers are sets that contain all numbers lesser than themselves.
  -- Examples:
  -- • 0: {}
  -- • 1: 0∪{0} = {0} = {{},{{}}}
  -- • 2: 1∪{1} = {0}∪{1} = {0,1} = {{},{{},{{}}}}
  -- • 3: 2∪{2} = {0,1}∪{2} = {0,1,2} = {{{},{{},{{}}}},{{{},{{},{{}}}}}}
  -- • 4: 3∪{3} = {0,1,2}∪{3} = {0,1,2,3} = {{{{},{{},{{}}}},{{{},{{},{{}}}}}},{{{{},{{},{{}}}},{{{},{{},{{}}}}}}}}
  𝐒 : S → S
  𝐒(n) = n ∪ singleton(n)

  𝟏 : S
  𝟏 = 𝐒(𝟎)

  -- A set is ℕ-inductive when has zero and all its successors.
  -- In loose terms: Inductive(I) means (I ⊆ ℕ)
  Inductive : S → Type
  Inductive(I) = (𝟎 ∈ I) ∧ (∀ₗ(x ↦ ((x ∈ I) → (𝐒(x) ∈ I))))

  field
    -- Set identity is extensionally determined. More specifically by its contents.
    set-extensionality : SetEqualityMembership(_≡ₑ_)

    -- `∅` is a set which is empty.
    -- • Allows a construction of an empty set.
    empty : EmptyMembership(∅)

    -- `pair` is the construction of a set with two elements.
    -- • Allows a construction of a set with two elements.
    pairing : PairMembership(pair)

    -- `filter` is the set which is the subset of a set where all elements satisfies a predicate.
    restricted-comprehension : FilterMembership{ℓ = ℓ}(filter)

    -- `⋃` is the construction of a set which contains all the elements of a collection of sets.
    -- • Allows a construction of a set that is the union of some sets.
    union : BigUnionMembership(⋃)

    -- `℘` is the construction of a set which contains all the subsets of a set.
    -- • Allows a construction of a set that is the powerset of a set.
    power : PowerMembership(_⊆_)(℘)

    -- `map` is the construction of the image of a function restricted to a set.
    -- • The `map`-function on a function is a function from sets to sets.
    replacement : MapMembership(map)

    -- `inductiveSet` is ℕ-inductive.
    -- • An inductive set is infinite, so this implies that an infinite set exists.
    -- • Makes it possible to construct the set of natural numbers (ℕ).
    infinity : Inductive(ω₀)

    -- A non-empty set contain sets that are disjoint to it.
    -- • Prevents sets from containing themselves.
    -- • Makes every set have an ordinal rank.
    regularity :  ∀ₗ(s₁ ↦ (NonEmpty(s₁) → ∃(s₂ ↦ (s₂ ∈ s₁) ∧ Disjoint(s₁)(s₂))))

    --choice : (∀{a} → (a ∈ A) → NonEmpty(a)) → PairwiseDisjoint(A) → ∃(b ↦ ∀{a} → (a ∈ A) → ∃!(_∈ (a ∩ b)))
    --choice : ∀{A B} ⦃ AB : A ⊇ B ⦄ ⦃ ne-B ⦄ → (choose(A)(B) ⦃ AB ⦄ ⦃ ne-B ⦄ ∈ B)
    -- The values of a choice function of a family of sets are all in the given sets.
    -- This states that a choice function actually chooses an element from the specified set.
    -- Note: A variant without the mentioning of `A` and a proof of `a ∈ A` would instead lead to the formulation of the axiom of global choice. The reason for not using global choice as an axiom is because unlike global choice, this variant makes every choice function expressable as a set. This variant should be interpreted as there being different choice functions for every family of sets. For example, when `A ≢ B`, `x ∈ A` and `x ∈ B` is satisfied, then `choose(A)(x) ≡ choose(B)(x)` should not neccesarily be satisfied while still (choose(A)(x) ∈ x) and (choose(B)(x) ∈ x).
    -- Examples:
    --   choose {ℕ,ℤ,ℚ,ℝ} ℝ ∈ ℝ
    --   choose {ℕ,ℤ,ℚ,ℝ} ℝ ≢ choose {ℤ,ℚ,ℝ} ℝ
    --   For example, it could be the case that (choose {ℕ,ℤ,ℚ,ℝ} ℝ = 0) but (choose {ℤ,ℚ,ℝ} ℝ = 1).
    -- Note: Without `choose-function`, `choice` would not be an actual choice function.
    choice : ∀{A a} → ⦃ ne : NonEmpty(a) ⦄ ⦃ aA : a ∈ A ⦄ → (choose A a ∈ a)
    ⦃ choose-function ⦄ : BinaryOperator(choose)

  𝑇 = 𝟎
  𝐹 = 𝟏
  BoolSet = pair 𝑇 𝐹

  instance
    Inductive-unaryRelator : UnaryRelator(Inductive)
    Inductive-unaryRelator = [∧]-unaryRelator ⦃ rel-P = binary-unaryRelatorₗ ⦄ ⦃ rel-Q = [∀]-unaryRelator ⦃ rel-P = [→]-unaryRelator ⦃ rel-P = binary-unaryRelatorₗ ⦄ ⦃ rel-Q = binary-unaryRelatorₗ ⦄ ⦄ ⦄

  open import Logic.Predicate.Theorems
  open import Logic.Propositional.Theorems
  open import Structure.Relator.Properties
  open import Structure.Relator.Proofs renaming ([≡]-binaryRelator to [≡ₑ]-binaryRelator)

  instance
    [≡]-binaryRelator : BinaryRelator(_≡_)
    BinaryRelator.substitution [≡]-binaryRelator xy₁ xy₂ x₁x₂ = [↔]-to-[→] set-extensionality (BinaryRelator.substitution [≡ₑ]-binaryRelator xy₁ xy₂ ([↔]-to-[←] set-extensionality x₁x₂))

  instance
    [⊆]-binaryRelator : BinaryRelator(_⊆_)
    BinaryRelator.substitution [⊆]-binaryRelator p1 p2 sub = [↔]-to-[→] ([↔]-to-[→] set-extensionality p2) ∘ sub ∘ [↔]-to-[←] ([↔]-to-[→] set-extensionality p1)

  instance
    pair-binaryOperator : BinaryOperator(pair)
    BinaryOperator.congruence pair-binaryOperator p1 p2 = [↔]-to-[←] set-extensionality (\{x} → [↔]-transitivity pairing ([↔]-transitivity ([∨]-map-[↔] (substitute₂ₗᵣ(_≡ₑ_) ⦃ [≡ₑ]-binaryRelator ⦄ (reflexivity(_≡ₑ_) {x}) p1) (substitute₂ₗᵣ(_≡ₑ_) ⦃ [≡ₑ]-binaryRelator  ⦄ (reflexivity(_≡ₑ_) {x}) p2)) ([↔]-symmetry pairing)))

  instance
    ℘-function : Function(℘)
    Function.congruence ℘-function xy = [↔]-to-[←] set-extensionality \{x} → [↔]-transitivity power ([↔]-transitivity ([↔]-intro (substitute₂ᵣ(_⊆_) ⦃ [⊆]-binaryRelator ⦄ (symmetry(_≡ₑ_) xy)) (substitute₂ᵣ(_⊆_) ⦃ [⊆]-binaryRelator ⦄ xy)) ([↔]-symmetry power))

  instance
    ⋃-function : Function(⋃)
    Function.congruence ⋃-function xy = [↔]-to-[←] set-extensionality \{x} → [↔]-transitivity union ([↔]-transitivity ([∃]-map-proof-[↔] ([∧]-map-[↔] ([↔]-to-[→] set-extensionality xy) [↔]-reflexivity)) ([↔]-symmetry union))

  filter-function : ∀ ⦃ rel-P : UnaryRelator(P) ⦄ ⦃ rel-Q : UnaryRelator(Q) ⦄ → (∀{x} → P(x) ↔ Q(x)) → ∀{A B} → (A ≡ₑ B) → (filter P(A) ≡ₑ filter Q(B))
  filter-function PQ AB = [↔]-to-[←] set-extensionality ([↔]-transitivity restricted-comprehension ([↔]-transitivity ([∧]-map-[↔] ([↔]-to-[→] set-extensionality AB) PQ) ([↔]-symmetry restricted-comprehension)))

  map-function : ∀{f} ⦃ func-f : Function(f) ⦄ {g} ⦃ func-g : Function(g) ⦄ → (f ⊜ g) → ∀{A B} → (A ≡ₑ B) → (map f(A) ≡ₑ map g(B))
  map-function {f = f}{g = g} (intro fg) {A = A}{B = B} AB = [↔]-to-[←] set-extensionality $ \{y} →
    (y ∈ map f A)        ⇔-[ replacement ]
    ∃ₛ(A)(x ↦ f(x) ≡ₑ y) ⇔-[ [∃]-map-proof-[↔] (\{x} → [∧]-map-[↔] ([↔]-to-[→] set-extensionality AB) (substitute₂ₗᵣ(_≡ₑ_) ⦃ [≡ₑ]-binaryRelator ⦄ (fg{x}) (reflexivity(_≡ₑ_)))) ]
    ∃ₛ(B)(x ↦ g(x) ≡ₑ y) ⇔-[ replacement ]-sym
    (y ∈ map g B)        ⇔-end

  [∪]-inclusion : UnionMembership(_∪_)
  [∪]-inclusion {A = A}{B = B}{x = x} =
    (x ∈ ⋃ (pair A B))                                    ⇔-[ union ]
    ∃(y ↦ (y ∈ pair A B) ∧ (x ∈ y))                       ⇔-[ [∃]-map-proof-[↔] (\{y} →
      (y ∈ pair A B) ∧ (x ∈ y)                    ⇔-[ [∧]-map-[↔] pairing [↔]-reflexivity ]
      ((y ≡ₑ A) ∨ (y ≡ₑ B)) ∧ (x ∈ y)             ⇔-[ [∧][∨]-distributivityᵣ ]
      ((y ≡ₑ A) ∧ (x ∈ y)) ∨ ((y ≡ₑ B) ∧ (x ∈ y)) ⇔-end
    ) ]
    ∃(y ↦ ((y ≡ₑ A) ∧ (x ∈ y)) ∨ ((y ≡ₑ B) ∧ (x ∈ y)))    ⇔-[ [∃][∨]-distributivity ]
    ∃(y ↦ (y ≡ₑ A) ∧ (x ∈ y)) ∨ ∃(y ↦ (y ≡ₑ B) ∧ (x ∈ y)) ⇔-[ [∨]-map-[↔] (p ⦃ rel = binary-unaryRelatorₗ ⦄) (p ⦃ rel = binary-unaryRelatorₗ ⦄) ]
    (x ∈ A) ∨ (x ∈ B)                                     ⇔-end
    where
      -- TODO: Maybe move this somewhere else
      p : ∀{T : Type{ℓ₁}} ⦃ equiv : Equiv{ℓₑ₁}(T) ⦄ {P : T → Type{ℓ₂}} ⦃ rel : UnaryRelator(P) ⦄ {y} → ∃(x ↦ (x ≡ₑ y) ∧ P(x)) ↔ P(y)
      p {P = P} = [↔]-intro (py ↦ [∃]-intro _ ⦃ [∧]-intro (reflexivity(_≡ₑ_)) py ⦄) (\([∃]-intro x ⦃ [∧]-intro xy px ⦄) → substitute₁(P) xy px)

  BoolSet-inclusion : (x ∈ BoolSet) ↔ (x ≡ₑ 𝑇) ∨ (x ≡ₑ 𝐹)
  BoolSet-inclusion = pairing

  pair-contains-left : a ∈ pair a b
  pair-contains-left = [↔]-to-[←] pairing ([∨]-introₗ (reflexivity(_≡ₑ_)))

  pair-contains-right : b ∈ pair a b
  pair-contains-right = [↔]-to-[←] pairing ([∨]-introᵣ (reflexivity(_≡ₑ_)))

  𝑇-in-BoolSet : 𝑇 ∈ BoolSet
  𝑇-in-BoolSet = pair-contains-left

  𝐹-in-BoolSet : 𝐹 ∈ BoolSet
  𝐹-in-BoolSet = pair-contains-right

  ℘-self : (A ∈ ℘(A))
  ℘-self = [↔]-to-[←] power id

  pair-superset : (x ∈ A) → (y ∈ A) → (pair x y ⊆ A)
  pair-superset pa pb p = [∨]-elim
    (eq ↦ substitute₂ₗ(_∈_) (symmetry(_≡ₑ_) eq) pa)
    (eq ↦ substitute₂ₗ(_∈_) (symmetry(_≡ₑ_) eq) pb)
    ([↔]-to-[→] pairing p)

  pair-superset-union : (a ∈ A) → (b ∈ B) → (pair a b ⊆ (A ∪ B))
  pair-superset-union pa pb p = pair-superset (([↔]-to-[←] [∪]-inclusion ∘ [∨]-introₗ) pa) (([↔]-to-[←] [∪]-inclusion ∘ [∨]-introᵣ) pb) p

  instance
    postulate [≡][⊆]-sub : (_≡_) ⊆₂ (_⊆_)

  instance
    postulate [⊆]-transitivity : Transitivity(_⊆_)

  open import Data.Either as Either using ()
  import      Data.Tuple as Tuple
  open import Syntax.Transitivity
  open import Syntax.Implication

  [≡][≢]-semitransitivityₗ : (a ≡ₑ b) → (b ≢ c) → (a ≢ c)
  [≡][≢]-semitransitivityₗ ab nbc ac = nbc(symmetry(_≡ₑ_) ab 🝖 ac)

  [≡][≢]-semitransitivityᵣ : (a ≢ b) → (b ≡ₑ c) → (a ≢ c)
  [≡][≢]-semitransitivityᵣ nab bc ac = nab(ac 🝖 symmetry(_≡ₑ_) bc)

  nonEmpty-filter : NonEmpty(filter P ⦃ unaryRel ⦄ A) ↔ ∃ₛ(A) P
  nonEmpty-filter = [∃]-map-proof-[↔] restricted-comprehension

  open import Function.Proofs

  instance
    singleton-function : Function(singleton)
    singleton-function = [$₂]-function

  singleton-inclusion : SingletonMembership(singleton)
  singleton-inclusion {y = y}{x = x} =
    x ∈ pair y y        ⇔-[ pairing ]
    (x ≡ₑ y) ∨ (x ≡ₑ y) ⇔-[ [∨]-redundancy ]
    x ≡ₑ y              ⇔-end

  singleton-contains-element : a ∈ singleton a
  singleton-contains-element = [↔]-to-[←] singleton-inclusion (reflexivity(_≡ₑ_))

  singleton-nonempty : NonEmpty(singleton x)
  singleton-nonempty{x = x} = [∃]-intro x ⦃ singleton-contains-element ⦄

  singleton-superset : (a ∈ A) → (singleton a ⊆ A)
  singleton-superset pa p = substitute₂ₗ(_∈_) (symmetry(_≡ₑ_) ([↔]-to-[→] singleton-inclusion p)) pa

  zero-one-ineq : (𝟎 ≢ 𝟏)
  zero-one-ineq p =
    p ⇒
    𝟎 ≡ₑ 𝟏            ⇒-[ p ↦ [↔]-to-[→] set-extensionality p {𝟎} ]
    (𝟎 ∈ 𝟎) ↔ (𝟎 ∈ 𝟏) ⇒-[ [↔]-to-[←] ]
    (𝟎 ∈ 𝟎) ← (𝟎 ∈ 𝟏) ⇒-[ apply ([↔]-to-[←] [∪]-inclusion ([∨]-introᵣ ([↔]-to-[←] singleton-inclusion (reflexivity(_≡ₑ_))))) ]
    (𝟎 ∈ 𝟎)           ⇒-[ empty ]
    ⊥                 ⇒-end
