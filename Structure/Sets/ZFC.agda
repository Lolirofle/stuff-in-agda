open import Type
open import Structure.Relator
open import Structure.Setoid.WithLvl renaming (_≡_ to _≡ₑ_)

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
open import Syntax.Function

private variable ℓ ℓₑ₁ : Lvl.Level
private variable A B C D E a b c d e x y z As : S
private variable f g h : S → S
private variable P Q R : S → Type{ℓ}
private variable ⦃ func ⦄ : Function ⦃ equiv ⦄ ⦃ equiv ⦄ (f)
private variable ⦃ unaryRel ⦄ : UnaryRelator ⦃ equiv ⦄ (P)

-- Containment
-- (a ∋ x) means that the set a contains the set x.
_∋_ = swap(_∈_)

-- Not element of
_∉_ = (¬_) ∘₂ (_∈_)

-- Non-containment
_∌_ = (¬_) ∘₂ (_∋_)

-- Set equality
_≡_ : S → S → Type
A ≡ B = ∀{x} → (x ∈ A) ↔ (x ∈ B)

-- Subset of
_⊆_ : S → S → Type
A ⊆ B = ∀{x} → (x ∈ A) → (x ∈ B)

-- Superset of
_⊇_ = swap(_⊆_)

∃ₛ : S → (S → Type{ℓ}) → Type
∃ₛ(A) P = ∃(x ↦ (x ∈ A) ∧ P(x))

∀ₛ : S → (S → Type{ℓ}) → Type
∀ₛ(A) P = ∀ₗ(x ↦ ((x ∈ A) → P(x)))

-- The statement that the set s is empty
Empty : S → Type
Empty(s) = ∀ₗ(x ↦ ¬(x ∈ s))

-- The statement that the set s is non-empty
NonEmpty : S → Type
NonEmpty(s) = ∃(_∈ s)

-- The statement that the set s is a set that contains all sets
Universal : S → Type
Universal(s) = ∀ₗ(x ↦ (x ∈ s))

-- The statement that the sets s₁ and s₂ are disjoint
Disjoint : S → S → Type
Disjoint(s₁)(s₂) = ∀ₗ(x ↦ ¬((x ∈ s₁)∧(x ∈ s₂)))
-- ¬ ∃ₗ(x ↦ (x ∈ s₁)∧(x ∈ s₂))

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
Pairwise : (S → S → Type{ℓ}) → (S → Type)
Pairwise Related (S) = ∀ₛ(S)(a ↦ ∀ₛ(S)(b ↦ ((a ≢ b) → Related(a)(b))))

[∃ₛ]-unaryRelator : ∀{P : S → S → Type{ℓ}} → ⦃ rel-P : ∀{x} → UnaryRelator(P(x)) ⦄ → UnaryRelator(\y → ∃ₛ(A)(x ↦ P(x)(y)))
[∃ₛ]-unaryRelator = [∃]-unaryRelator ⦃ rel-P = [∧]-unaryRelator ⦄

[∀ₛ]-unaryRelator : ∀{P : S → S → Type{ℓ}} → ⦃ rel-P : ∀{x} → UnaryRelator(P(x)) ⦄ → UnaryRelator(\y → ∀ₛ(A)(x ↦ P(x)(y)))
[∀ₛ]-unaryRelator = [∀]-unaryRelator ⦃ rel-P = [→]-unaryRelator ⦄

[∃ₛ]-binaryRelator : ∀{P : S → S → S → Type{ℓ}} → ⦃ rel-P : ∀{x} → BinaryRelator(P(x)) ⦄ → BinaryRelator(\A y → ∃ₛ(A)(x ↦ P(x)(A)(y)))
[∃ₛ]-binaryRelator = binaryRelator-from-unaryRelator
  ⦃ relₗ = [∃]-unaryRelator ⦃ rel-P = [∧]-unaryRelator ⦃ rel-P = binary-unaryRelatorₗ ⦄ ⦃ rel-Q = binary-unaryRelatorᵣ ⦄ ⦄ ⦄
  ⦃ relᵣ = [∃]-unaryRelator ⦃ rel-P = [∧]-unaryRelator ⦃ rel-Q = binary-unaryRelatorₗ ⦄ ⦄ ⦄

[∀ₛ]-binaryRelator : ∀{P : S → S → S → Type{ℓ}} → ⦃ rel-P : ∀{x} → BinaryRelator(P(x)) ⦄ → BinaryRelator(\A y → ∀ₛ(A)(x ↦ P(x)(A)(y)))
[∀ₛ]-binaryRelator = binaryRelator-from-unaryRelator
  ⦃ relₗ = [∀]-unaryRelator ⦃ rel-P = [→]-unaryRelator ⦃ rel-P = binary-unaryRelatorₗ ⦄ ⦃ rel-Q = binary-unaryRelatorᵣ ⦄ ⦄ ⦄
  ⦃ relᵣ = [∀]-unaryRelator ⦃ rel-P = [→]-unaryRelator ⦃ rel-Q = binary-unaryRelatorₗ ⦄ ⦄ ⦄

record ZFC : Typeω where
  infixl 3000 _∪_
  infixl 3001 _∩_
  infixl 3002 _⨯_ _∖_

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

    -- A choice function for non-empty sets.
    -- Chooses an arbitrary element in a non-empty set.
    -- choose : (A B : S) → ⦃ A ⊇ B ⦄ → ⦃ NonEmpty(B) ⦄ → S
    choose : (A a : S) → ⦃ NonEmpty(a) ⦄ →  ⦃ a ∈ A ⦄ → S

  -- Singleton set.
  -- A set consisting of only a single element.
  singleton : S → S
  singleton(s) = pair(s)(s)

  -- Union operator.
  -- Constructs a set which consists of both elements from LHS and RHS.
  _∪_ : S → S → S
  a ∪ b = ⋃(pair a b)

  -- Intersection operator.
  -- Constructs a set which consists of elements which are in both LHS and RHS.
  _∩_ : S → S → S
  a ∩ b = filter(_∈ a) ⦃ binary-unaryRelatorᵣ ⦄ (b)

  -- "Without"-operator.
  -- Constructs a set which consists of elements which are in LHS, but not RHS.
  _∖_ : S → S → S
  a ∖ b = filter(_∉ a) ⦃ [¬]-unaryRelator ⦃ rel-P = binary-unaryRelatorᵣ ⦄ ⦄ (b)

  -- Intersection over arbitrary sets.
  -- Constructs a set which consists of elements which are in all of the specified sets.
  ⋂ : S → S
  ⋂(a) = filter(a₁ ↦ (∀{a₂} → (a₂ ∈ a) → (a₁ ∈ a₂))) ⦃ [∀]-unaryRelator ⦃ rel-P = [→]-unaryRelator ⦃ rel-Q = binary-unaryRelatorᵣ ⦄ ⦄ ⦄ (⋃(a))

  -- Tuple value.
  -- An ordered pair of values.
  _,_ : S → S → S
  a , b = pair(singleton(a)) (pair(a)(b))

  -- Set product (Set of tuples) (Cartesian product).
  _⨯_ : S → S → S
  a ⨯ b = filter(t ↦ ∃ₛ(a)(x ↦ ∃ₛ(b)(y ↦ t ≡ₑ (x , y)))) ⦃ [∃ₛ]-unaryRelator ⦃ rel-P = [∃ₛ]-unaryRelator ⦃ rel-P = binary-unaryRelatorᵣ ⦃ rel-P = [≡ₑ]-binaryRelator ⦄ ⦄ ⦄ ⦄ (℘(℘(a ∪ b))) -- [∃ₛ]-unaryRelator ⦃ rel-P = [∃ₛ]-unaryRelator ⦃ rel-P = {!!} ⦄ ⦄

  identityPair : S → S
  identityPair(D) = filter(xy ↦ ∃(a ↦ xy ≡ₑ (a , a))) ⦃ [∃]-unaryRelator ⦃ rel-P = binary-unaryRelatorᵣ ⦃ rel-P = [≡ₑ]-binaryRelator ⦄ ⦄ ⦄ (D ⨯ D)

  -- Quotient set.
  -- The set of equivalence classes.
  _/_ : S → (_▫_ : S → S → Type{ℓ}) ⦃ rel : BinaryRelator(_▫_) ⦄ → S
  (a / (_▫_)) ⦃ rel ⦄ = filter(aₛ ↦ ∀ₛ(aₛ)(x ↦ ∀ₛ(aₛ)(x ▫_))) ⦃ binary-unaryRelatorᵣ ⦃ rel-P = [∀ₛ]-binaryRelator {P = \x A _ → ∀ₛ(A) (x ▫_)} ⦃ rel-P = [∀ₛ]-binaryRelator ⦃ rel-P = const-binaryRelator ⦄ ⦄ ⦄ {∅} ⦄ (℘(a))
  -- binary-unaryRelatorᵣ ⦃ rel-P = [∀ₛ]-binaryRelator ⦃ rel-P = {!!} ⦄ ⦄

  -- Equivalence class
  -- The set of elements which are equivalent to the specified one.
  [_of_,_] : S → S → (_▫_ : S → S → Type{ℓ}) ⦃ rel : BinaryRelator(_▫_) ⦄ → S
  [ x of a , (_▫_) ] = filter(x ▫_) ⦃ binary-unaryRelatorₗ ⦄ (a)

  -- The unmap of a set.
  -- The set of elements in the domain X when applied to a function gives an element in Y.
  -- Or: The inverse image of the function on the set.
  -- Or: The pre-image of the function on the set.
  -- Note:
  --   The domain is neccessary because a class function's domain is not neccesarily a set.
  --   For example: `const(x): Domain → Domain` for any (x: Domain) is a class function for which its domain is not a set.
  --   This is because const is defined for all objects in `Domain`, so if a set would have to have all objects in `Domain`, it has to be the universal set, but there is no universal set.
  unmap : S → (f : S → S) ⦃ func : Function(f) ⦄ → S → S
  unmap(X) f(Y) = filter(x ↦ f(x) ∈ Y) ⦃ [∘]-unaryRelator {P = _∈ Y} ⦃ binary-unaryRelatorᵣ ⦄ ⦄ (X)

  -- The zero constant from the standard inductive set definition of ℕ in ZFC set theory.
  𝟎 : S
  𝟎 = ∅

  -- The successor function from the standard inductive set definition of ℕ in ZFC set theory.
  -- This means that all lesser numbers are contained in every number.
  -- Examples:
  -- • 0: {}
  -- • 1: 0∪{0} = {0} = {{},{{}}}
  -- • 2: 1∪{1} = {0}∪{1} = {0,1} = {{},{{},{{}}}}
  -- • 3: 2∪{2} = {0,1}∪{2} = {0,1,2} = {{{},{{},{{}}}},{{{},{{},{{}}}}}}
  -- • 4: 3∪{3} = {0,1,2}∪{3} = {0,1,2,3} = {{{{},{{},{{}}}},{{{},{{},{{}}}}}},{{{{},{{},{{}}}},{{{},{{},{{}}}}}}}}
  𝐒 : S → S
  𝐒(n) = n ∪ singleton(n)

  -- A set is ℕ-inductive when has zero and all its successors.
  -- In loose terms: Inductive(I) means (I ⊆ ℕ)
  Inductive : S → Type
  Inductive(I) = (𝟎 ∈ I) ∧ (∀ₗ(x ↦ ((x ∈ I) → (𝐒(x) ∈ I))))

  instance
    Inductive-unaryRelator : UnaryRelator(Inductive)
    Inductive-unaryRelator = [∧]-unaryRelator ⦃ rel-P = binary-unaryRelatorₗ ⦄ ⦃ rel-Q = [∀]-unaryRelator ⦃ rel-P = [→]-unaryRelator ⦃ rel-P = binary-unaryRelatorₗ ⦄ ⦃ rel-Q = binary-unaryRelatorₗ ⦄ ⦄ ⦄

  -- The "smallest" inductive set is the set of natural numbers.
  -- All elements which can be expressed using only 𝟎 and 𝐒.
  ℕ : S
  ℕ = ⋂(filter Inductive (℘(ω₀))) -- TODO: This pattern seems useful

  -- The relation "lesser than" in this model of ℕ.
  -- This works for all elements in ℕ by the definition of 𝟎 and 𝐒.
  _<_ : S → S → Type
  a < b = a ∈ b

  _≤_ : S → S → Type
  a ≤ b = (a < b) ∨ (a ≡ b)

  _>_ : S → S → Type
  a > b = b < a

  _≥_ : S → S → Type
  a ≥ b = b ≤ a

  infixl 2000 _<_ _≤_ _>_ _≥_

  𝕟 : S → S
  𝕟(n) = filter(_< n) ⦃ binary-unaryRelatorᵣ ⦄ (ℕ)

  𝑇 = 𝟎
  𝐹 = 𝐒 𝟎
  BoolSet = pair 𝑇 𝐹

  field
    -- Set identity is extensionally determined. More specifically by its contents.
    set-extensionality : (A ≡ B) ↔ (A ≡ₑ B)

    -- `∅` is a set which is empty.
    -- • Allows a construction of an empty set.
    empty : ∀{x} → (x ∉ ∅)

    -- `pair` is the construction of a set with two elements.
    -- • Allows a construction of a set with two elements.
    pairing : ∀{x} → (x ∈ pair A B) ↔ ((x ≡ₑ A) ∨ (x ≡ₑ B))
    
    -- `filter` is the set which is the subset of a set where all elements satisfies a predicate.
    restricted-comprehension : ∀{x} → (x ∈ filter{ℓ} P ⦃ unaryRel ⦄ (A)) ↔ ((x ∈ A) ∧ P(x))

    -- `⋃` is the construction of a set which contains all the elements of a collection of sets.
    -- • Allows a construction of a set that is the union of some sets.
    union : ∀{x} → (x ∈ ⋃(As)) ↔ ∃(A ↦ (A ∈ As) ∧ (x ∈ A))

    -- `℘` is the construction of a set which contains all the subsets of a set.
    -- • Allows a construction of a set that is the powerset of a set.
    power : ∀{x} → (x ∈ ℘(y)) ↔ (x ⊆ y)

    -- `map` is the construction of the image of a function restricted to a set.
    -- • The `map`-function on a function is a function from sets to sets.
    replacement : ∀{y} → (y ∈ map f ⦃ func ⦄ (A)) ↔ ∃ₛ(A)(x ↦ y ≡ f(x))

    -- `inductiveSet` is ℕ-inductive.
    -- • An inductive set is infinite, so this implies that an infinite set exists.
    -- • Makes it possible to construct the set of natural numbers (ℕ).
    infinity : Inductive(ω₀)

    -- A non-empty set contain sets that are disjoint to it.
    -- • Prevents sets containing themselves.
    -- • Makes every set have an ordinal rank.
    regularity :  ∀ₗ(s₁ ↦ (NonEmpty(s₁) → ∃(s₂ ↦ (s₂ ∈ s₁) ∧ Disjoint(s₁)(s₂))))

    --choice : (∀{a} → (a ∈ A) → NonEmpty(a)) → PairwiseDisjoint(A) → ∃(b ↦ ∀{a} → (a ∈ A) → ∃!(_∈ (a ∩ b)))
    --choice : ∀{A B} ⦃ AB : A ⊇ B ⦄ ⦃ ne-B ⦄ → (choose(A)(B) ⦃ AB ⦄ ⦃ ne-B ⦄ ∈ B)
    -- The values of a choice function of a family of sets are all in the given sets.
    -- This states that a choice function actually chooses an element from the specified set.
    -- Note: The mention of `A` and a proof of `a ∈ A` is neccessary to guarantee that the extensionality properties are correct. There are different choice functions for every family of sets. For example, when `A ≢ B`, `x ∈ A` and `x ∈ B` is satisfied, then `choose(A)(x) ≡ choose(B)(x)` should not be satisfied. A slight modification of this (disgarding the mention of `A` leads to the formulation of the axiom of global choice).
    choice : ∀{A a} → ⦃ ne : NonEmpty(a) ⦄ ⦃ aA : a ∈ A ⦄ → (choose A a ∈ a)
    choose-function : ∀{A a} → ⦃ nea : NonEmpty(a) ⦄ →  ⦃ aA : a ∈ A ⦄ → ∀{B b} → ⦃ neb : NonEmpty(b) ⦄ →  ⦃ bB : b ∈ B ⦄ → (A ≡ₑ B) → (a ≡ₑ b) → (choose A a ≡ₑ choose B b) -- TODO: This is not provable from the other axioms, I think? Note that this should be true, or otherwise it would not be a "choice"

  open import Logic.Predicate.Theorems
  open import Logic.Propositional.Theorems
  open import Structure.Relator.Properties
  open import Structure.Relator.Proofs renaming ([≡]-binaryRelator to [≡ₑ]-binaryRelator)

  instance
    [≡]-binaryRelator : BinaryRelator(_≡_)
    BinaryRelator.substitution [≡]-binaryRelator xy₁ xy₂ x₁x₂ = [↔]-to-[←] set-extensionality (BinaryRelator.substitution [≡ₑ]-binaryRelator xy₁ xy₂ ([↔]-to-[→] set-extensionality x₁x₂))

  instance
    [⊆]-binaryRelator : BinaryRelator(_⊆_)
    BinaryRelator.substitution [⊆]-binaryRelator p1 p2 sub = [↔]-to-[→] ([↔]-to-[←] set-extensionality p2) ∘ sub ∘ [↔]-to-[←] ([↔]-to-[←] set-extensionality p1)

  instance
    pair-binaryOperator : BinaryOperator(pair)
    BinaryOperator.congruence pair-binaryOperator p1 p2 = [↔]-to-[→] set-extensionality (\{x} → [↔]-transitivity pairing ([↔]-transitivity ([∨]-map-[↔] (substitute₂ₗᵣ(_≡ₑ_) ⦃ [≡ₑ]-binaryRelator ⦄ (reflexivity(_≡ₑ_) {x}) p1) (substitute₂ₗᵣ(_≡ₑ_) ⦃ [≡ₑ]-binaryRelator  ⦄ (reflexivity(_≡ₑ_) {x}) p2)) ([↔]-symmetry pairing)))

  instance
    ℘-function : Function(℘)
    Function.congruence ℘-function xy = [↔]-to-[→] set-extensionality \{x} → [↔]-transitivity power ([↔]-transitivity ([↔]-intro (substitute₂ᵣ(_⊆_) ⦃ [⊆]-binaryRelator ⦄ (symmetry(_≡ₑ_) xy)) (substitute₂ᵣ(_⊆_) ⦃ [⊆]-binaryRelator ⦄ xy)) ([↔]-symmetry power))

  instance
    ⋃-function : Function(⋃)
    Function.congruence ⋃-function xy = [↔]-to-[→] set-extensionality \{x} → [↔]-transitivity union ([↔]-transitivity ([∃]-map-proof-[↔] ([∧]-map-[↔] ([↔]-to-[←] set-extensionality xy) [↔]-reflexivity)) ([↔]-symmetry union))

  filter-function : ∀ ⦃ rel-P : UnaryRelator(P) ⦄ ⦃ rel-Q : UnaryRelator(Q) ⦄ → (∀{x} → P(x) ↔ Q(x)) → ∀{A B} → (A ≡ₑ B) → (filter P(A) ≡ₑ filter Q(B))
  filter-function PQ AB = [↔]-to-[→] set-extensionality ([↔]-transitivity restricted-comprehension ([↔]-transitivity ([∧]-map-[↔] ([↔]-to-[←] set-extensionality AB) PQ) ([↔]-symmetry restricted-comprehension)))

  map-function : ∀{f} ⦃ func-f : Function(f) ⦄ {g} ⦃ func-g : Function(g) ⦄ → (f ⊜ g) → ∀{A B} → (A ≡ₑ B) → (map f(A) ≡ₑ map g(B))
  map-function (intro fg) AB = [↔]-to-[→] set-extensionality ([↔]-transitivity replacement ([↔]-transitivity ([∃]-map-proof-[↔] (\{x} → [∧]-map-[↔] ([↔]-to-[←] set-extensionality AB) (substitute₂ₗᵣ(_≡_) ⦃ [≡]-binaryRelator ⦄ (reflexivity(_≡ₑ_)) (fg{x})))) ([↔]-symmetry replacement)))

  postulate [∪]-inclusion : ∀{x} → (x ∈ A ∪ B) ↔ ((x ∈ A) ∨ (x ∈ B))

  postulate singleton-inclusion : ∀{x} → (x ∈ singleton A) ↔ (x ≡ₑ A)

  BoolSet-inclusion : ∀{x} → (x ∈ BoolSet) ↔ (x ≡ₑ 𝑇) ∨ (x ≡ₑ 𝐹)
  BoolSet-inclusion = pairing

  pair-contains-left : a ∈ pair a b
  pair-contains-left = [↔]-to-[←] pairing ([∨]-introₗ (reflexivity(_≡ₑ_)))

  pair-contains-right : b ∈ pair a b
  pair-contains-right = [↔]-to-[←] pairing ([∨]-introᵣ (reflexivity(_≡ₑ_)))

  𝑇-in-BoolSet : 𝑇 ∈ BoolSet
  𝑇-in-BoolSet = pair-contains-left

  𝐹-in-BoolSet : 𝐹 ∈ BoolSet
  𝐹-in-BoolSet = pair-contains-right

  singleton-nonempty : NonEmpty(singleton x)
  singleton-nonempty{x = x} = [∃]-intro x ⦃ [↔]-to-[←] singleton-inclusion (reflexivity(_≡ₑ_)) ⦄

  open import Data.Either as Either using ()
  import      Data.Tuple as Tuple
  open import Syntax.Transitivity
  open import Syntax.Implication

  zero-one-ineq : (𝟎 ≢ 𝐒 𝟎)
  zero-one-ineq p =
    p ⇒
    𝟎 ≡ₑ 𝐒 𝟎            ⇒-[ p ↦ [↔]-to-[←] set-extensionality p {𝟎} ]
    (𝟎 ∈ 𝟎) ↔ (𝟎 ∈ 𝐒 𝟎) ⇒-[ [↔]-to-[←] ]
    (𝟎 ∈ 𝟎) ← (𝟎 ∈ 𝐒 𝟎) ⇒-[ apply ([↔]-to-[←] [∪]-inclusion ([∨]-introᵣ ([↔]-to-[←] singleton-inclusion (reflexivity(_≡ₑ_))))) ]
    (𝟎 ∈ 𝟎)             ⇒-[ empty ]
    ⊥                   ⇒-end

  [≡][≢]-semitransitivityₗ : (a ≡ₑ b) → (b ≢ c) → (a ≢ c)
  [≡][≢]-semitransitivityₗ ab nbc ac = nbc(symmetry(_≡ₑ_) ab 🝖 ac)

  [≡][≢]-semitransitivityᵣ : (a ≢ b) → (b ≡ₑ c) → (a ≢ c)
  [≡][≢]-semitransitivityᵣ nab bc ac = nab(ac 🝖 symmetry(_≡ₑ_) bc)

  filter-nonEmpty : NonEmpty(filter P ⦃ unaryRel ⦄ A) ↔ ∃(x ↦ (x ∈ A) ∧ P(x))
  filter-nonEmpty = [∃]-map-proof-[↔] restricted-comprehension

  -- ZF with axiom of choice implies excluded middle.
  -- Note that this requires a number of different axioms: Set extensionality, axiom of choice, choice functions are functions, restricted set comprehension, the existence of at least two different sets, and a set that contains the two different sets.
  -- Also called: Diaconescu's theorem, Goodman–Myhill theorem.
  excluded-middle : ∀{P : Type{ℓ}} → (P ∨ (¬ P))
  excluded-middle{P = P} =
    • (
      (_⇒
        P                          ⇒-[ (\p {x} → [↔]-transitivity (pos-containment {x}) ([↔]-transitivity ([∧]-mapᵣ-[↔] ([↔]-intro (const([∨]-introₗ p)) (const([∨]-introₗ p)))) ([↔]-symmetry (neg-containment {x})))) ]
        (pos ≡ neg)                ⇒-[ [↔]-to-[→] set-extensionality ]
        (pos ≡ₑ neg)               ⇒-[ choose-function ⦃ ne-pos ⦄ ⦃ pair-contains-left ⦄ ⦃ ne-neg ⦄ ⦃ pair-contains-right ⦄ (reflexivity(_≡ₑ_)) ]
        (pos-choose ≡ₑ neg-choose) ⇒-end
      ) ⇒
      (P → (pos-choose ≡ₑ neg-choose))    ⇒-[ contrapositiveᵣ ]
      ((¬ P) ← (pos-choose ≢ neg-choose)) ⇒-end
    )
    • (
      • pos-choice
      • neg-choice
      ⇒₂-[ [∧]-intro ]
      (P ∨ (pos-choose ≡ 𝟎)) ∧ (P ∨ (neg-choose ≡ 𝐒 𝟎)) ⇒-[ [↔]-to-[←] [∨][∧]-distributivityₗ ]
      P ∨ ((pos-choose ≡ 𝟎) ∧ (neg-choose ≡ 𝐒 𝟎))       ⇒-[ Either.mapRight (\{([∧]-intro p0 n1) → [≡][≢]-semitransitivityᵣ([≡][≢]-semitransitivityₗ ([↔]-to-[→] set-extensionality p0) zero-one-ineq) (symmetry(_≡ₑ_) ([↔]-to-[→] set-extensionality n1))}) ]
      P ∨ (pos-choose ≢ neg-choose)                     ⇒-end
    )
    ⇒₂-[ Either.mapRight ]
    (P ∨ (¬ P)) ⇒-end
    where
      instance
        pos-rel : UnaryRelator(x ↦ P ∨ (x ≡ 𝟎))
        pos-rel = [∨]-unaryRelator ⦃ rel-Q = binary-unaryRelatorᵣ ⦄

      instance
        neg-rel : UnaryRelator(x ↦ P ∨ (x ≡ 𝐒 𝟎))
        neg-rel = [∨]-unaryRelator ⦃ rel-Q = binary-unaryRelatorᵣ ⦄

      pos = filter (x ↦ P ∨ (x ≡ 𝟎))   BoolSet
      neg = filter (x ↦ P ∨ (x ≡ 𝐒 𝟎)) BoolSet

      pos-containment : (x ∈ pos) ↔ (x ∈ BoolSet) ∧ (P ∨ (x ≡ 𝟎))
      pos-containment = restricted-comprehension

      neg-containment : (x ∈ neg) ↔ (x ∈ BoolSet) ∧ (P ∨ (x ≡ 𝐒 𝟎))
      neg-containment = restricted-comprehension

      instance
        ne-pos : NonEmpty(pos)
        ne-pos = [↔]-to-[←] (filter-nonEmpty) ([∃]-intro 𝟎 ⦃ [∧]-intro 𝑇-in-BoolSet ([∨]-introᵣ (\{_} → [↔]-reflexivity)) ⦄)

      instance
        ne-neg : NonEmpty(neg)
        ne-neg = [↔]-to-[←] (filter-nonEmpty) ([∃]-intro (𝐒 𝟎) ⦃ [∧]-intro 𝐹-in-BoolSet ([∨]-introᵣ (\{_} → [↔]-reflexivity)) ⦄)

      pos-choose = choose (pair pos neg) pos ⦃ ne-pos ⦄ ⦃ pair-contains-left ⦄
      neg-choose = choose (pair pos neg) neg ⦃ ne-neg ⦄ ⦃ pair-contains-right ⦄

      pos-choice : P ∨ (pos-choose ≡ 𝟎)
      pos-choice = [∧]-elimᵣ ([↔]-to-[→] pos-containment (choice {pair pos neg} {pos} ⦃ ne-pos ⦄ ⦃ pair-contains-left ⦄))

      neg-choice : P ∨ (neg-choose ≡ 𝐒 𝟎)
      neg-choice = [∧]-elimᵣ ([↔]-to-[→] neg-containment (choice {pair pos neg} {neg} ⦃ ne-neg ⦄ ⦃ pair-contains-right ⦄))
