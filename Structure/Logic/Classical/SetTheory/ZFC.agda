open import Functional hiding (Domain)
import      Structure.Logic.Classical.NaturalDeduction

module Structure.Logic.Classical.SetTheory.ZFC {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} ⦃ classicLogic : _ ⦄ (_∈_ : Domain → Domain → Formula) where
open Structure.Logic.Classical.NaturalDeduction.ClassicalLogic {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} (classicLogic)

open import Lang.Instance
import      Lvl
open import Structure.Logic.Classical.NaturalDeduction.Proofs         ⦃ classicLogic ⦄
open import Structure.Logic.Classical.SetTheory.BoundedQuantification ⦃ classicLogic ⦄ (_∈_)
open import Structure.Logic.Classical.SetTheory.Relation              ⦃ classicLogic ⦄ (_∈_)
open import Structure.Logic.Classical.SetTheory                       ⦃ classicLogic ⦄ (_∈_)
open import Structure.Logic.Constructive.Functions(Domain)
open import Structure.Logic.Constructive.Functions.Properties ⦃ constructiveLogicSignature ⦄

private
  module Meta where
    open import Numeral.FiniteStrict           public
    open import Numeral.FiniteStrict.Bound{ℓₗ} public
    open import Numeral.Natural                public

-- The symbols/signature of ZFC set theory.
record Signature : Set((ℓₗ Lvl.⊔ ℓₒ) Lvl.⊔ ℓₘₗ) where
  infixl 3000 _∪_
  infixl 3001 _∩_
  infixl 3002 _⨯_ _∖_

  field
    -- Empty set
    -- The set consisting of no elements.
    ∅ : Domain

    -- Pair set.
    -- The set consisting of only two elements.
    pair : Domain → Domain → Domain

    -- Subset filtering.
    -- The subset of the specified set where all elements satisfy the specified formula.
    filter : Domain → (Domain → Formula) → Domain

    -- Power set.
    -- The set of all subsets of the specified set.
    ℘ : Domain → Domain

    -- Union over arbitrary sets.
    -- Constructs a set which consists of elements which are in any of the specified sets.
    ⋃ : Domain → Domain

    -- An inductive set.
    -- A set which has the `Inductive`-property. Also infinite.
    inductiveSet : Domain

    -- The map of a set.
    -- The set of values when a function is applied to every element of a set.
    -- Or: The image of the function on the set.
    -- Or: The image of the function.
    map : (Domain → Domain) → Domain → Domain

    -- An inverse function of a function from its domain to its image.
    inv : (Domain → Domain) → Domain → Domain

  -- Singleton set.
  -- A set consisting of only a single element.
  singleton : Domain → Domain
  singleton(s) = pair(s)(s)

  -- Union operator.
  -- Constructs a set which consists of both elements from LHS and RHS.
  _∪_ : Domain → Domain → Domain
  a ∪ b = ⋃(pair a b)

  -- Intersection operator.
  -- Constructs a set which consists of elements which are in both LHS and RHS.
  _∩_ : Domain → Domain → Domain
  a ∩ b = filter(a)(_∈ b)

  -- "Without"-operator.
  -- Constructs a set which consists of elements which are in LHS, but not RHS.
  _∖_ : Domain → Domain → Domain
  a ∖ b = filter(a)(_∉ b)

  -- Intersection over arbitrary sets.
  -- Constructs a set which consists of elements which are in all of the specified sets.
  ⋂ : Domain → Domain
  ⋂(a) = filter(⋃(a)) (a₁ ↦ ∀ₗ(a₂ ↦ (a₂ ∈ a) ⟶ (a₁ ∈ a₂)))

  -- Tuple value.
  -- An ordered pair of values.
  _,_ : Domain → Domain → Domain
  a , b = pair(singleton(a)) (pair(a)(b))

  -- Set product (Set of tuples) (Cartesian product).
  _⨯_ : Domain → Domain → Domain
  a ⨯ b = filter(℘(℘(a ∪ b))) (t ↦ ∃ₗ(x ↦ (x ∈ a) ∧ ∃ₗ(y ↦ (y ∈ b) ∧ (t ≡ (x , y)))))

  identityPairing : Domain → Domain
  identityPairing(D) = filter(D ⨯ D) (xy ↦ ∃ₗ(a ↦ xy ≡ (a , a)))

  -- swappedPairing : Domain → Domain
  -- swappedPairing() = 

  -- Set product over a finite indexed family (Cartesian product).
  -- TODO: Not really like this. See definition of (_⨯_) and (_,_), and try to express the same here
  -- TODO: Also, make it possible to take the set product of infinite indexed families
  -- TODO: Maybe just use functions like (𝕟(n) →ₛₑₜ _) for finite and (ℕ → _) for infinite
  -- ∏_ : ∀{n} → FiniteIndexedFamily(n) → Domain
  -- ∏_ {Meta.𝟎}            _ = singleton(∅)
  -- ∏_ {Meta.𝐒(Meta.𝟎)}    I = I(Meta.𝟎)
  -- ∏_ {Meta.𝐒(Meta.𝐒(n))} I = I(Meta.maximum) ⨯ (∏_ {Meta.𝐒(n)} (I ∘ Meta.bound-𝐒))

  -- Quotient set.
  -- The set of equivalence classes.
  _/_ : Domain → BinaryRelator → Domain
  a / (_▫_) = filter(℘(a))(aₛ ↦ ∀ₛ(aₛ)(x ↦ ∀ₛ(aₛ)(y ↦ x ▫ y)))

  -- Equivalence class
  -- The set of elements which are equivalent to the specified one.
  [_of_,_] : Domain → Domain → BinaryRelator → Domain
  [ x of a , (_▫_) ] = filter(a)(y ↦ x ▫ y)

module Function ⦃ signature : Signature ⦄ where
  open Signature ⦃ ... ⦄

  record SetRepresentable (f : Function) : Set((ℓₗ Lvl.⊔ ℓₒ) Lvl.⊔ ℓₘₗ) where
    constructor intro

    field
      set : Domain

    field
      proof : Proof(∀ₗ(x ↦ ∀ₗ(y ↦ (f(x) ≡ y) ⟷ ((x , y) ∈ set))))

  -- An instance of Type(f) means that the function f has a default domain and codomain, and a proof that the function actually are closed inside this domain/codomain pair.
  record Type (f : Function) : Set((ℓₗ Lvl.⊔ ℓₒ) Lvl.⊔ ℓₘₗ) where
    constructor intro
    field
      domain   : Domain
      codomain : Domain

    field
      closure : Proof(∀ₛ(domain)(x ↦ f(x) ∈ codomain))
  open Type ⦃ ... ⦄ public

module BinaryRelatorSet ⦃ signature : Signature ⦄ where
  open Signature ⦃ ... ⦄

  -- Like:
  --   (x,f(x)) = (x , y)
  --   f = {(x , y)}
  --   = {{{x},{x,y}}}
  --   ⋃f = {{x},{x,y}}
  --   ⋃²f = {x,y}
  lefts : Domain → Domain
  lefts(s) = filter(⋃(⋃ s)) (x ↦ ∃ₗ(y ↦ (x , y) ∈ s))

  rights : Domain → Domain
  rights(s) = filter(⋃(⋃ s)) (y ↦ ∃ₗ(x ↦ (x , y) ∈ s))

  leftsOfMany : Domain → Domain → Domain
  leftsOfMany f(S) = filter(⋃(⋃ f)) (a ↦ ∃ₛ(S)(y ↦ (a , y) ∈ f))

  rightsOfMany : Domain → Domain → Domain
  rightsOfMany f(S) = filter(⋃(⋃ f)) (a ↦ ∃ₛ(S)(x ↦ (x , a) ∈ f))

  leftsOf : Domain → Domain → Domain
  leftsOf f(y) = leftsOfMany f(singleton(y))

  rightsOf : Domain → Domain → Domain
  rightsOf f(x) = rightsOfMany f(singleton(x))

  -- swap : Domain → Domain
  -- swap(s) = filter(rights(s) ⨯ left(s)) (xy ↦ )

module FunctionSet ⦃ signature : Signature ⦄ where
  open Signature ⦃ ... ⦄
  open BinaryRelatorSet ⦃ ... ⦄

  -- The set s can be interpreted as a function.
  FunctionSet : Domain → Formula
  FunctionSet(s) = ∀ₗ(x ↦ Unique(y ↦ (x , y) ∈ s))

  -- The set s can be interpreted as a function with a specified domain.
  -- The following describes the relation to the standard notation of functions:
  -- • ∀(x∊A)∀y. ((x,y) ∈ S) ⇔ (S(x) = y)
  Total : Domain → Domain → Formula
  Total(A)(s) = ∀ₛ(A)(x ↦ ∃ₗ(y ↦ (x , y) ∈ s))

  Injective' : Domain → Formula
  Injective'(f) = ∀ₗ(y ↦ Unique(x ↦ (x , y) ∈ f))

  Surjective' : Domain → Domain → Formula
  Surjective'(B)(f) = ∀ₛ(B)(y ↦ ∃ₗ(x ↦ (x , y) ∈ f))

  Bijective' : Domain → Domain → Formula
  Bijective'(B)(f) =
    Injective'(f)
    ∧ Surjective'(B)(f)

  -- The set of total function sets. All sets which can be interpreted as a total function.
  _^_ : Domain → Domain → Domain
  B ^ A = filter(℘(A ⨯ B)) (f ↦ FunctionSet(f) ∧ Total(A)(f))

  _→ₛₑₜ_ = swap _^_

  ⊷ : Domain → Domain
  ⊷ = lefts

  ⊶ : Domain → Domain
  ⊶ = rights

  map' : Domain → Domain → Domain
  map' = rightsOfMany

  unmap : Domain → Domain → Domain
  unmap = leftsOfMany

  apply-set : Domain → Domain → Domain
  apply-set = rightsOf

  unapply-set : Domain → Domain → Domain
  unapply-set = leftsOf

  _∘'_ : Domain → Domain → Domain
  _∘'_ f g = filter((⊷ f) ⨯ (⊶ g)) (a ↦ ∃ₗ(x ↦ ∃ₗ(y ↦ ∃ₗ(a₁ ↦ ((a₁ , y) ∈ f) ∧ ((x , a₁) ∈ g)) ∧ (a ≡ (x , y)))))

  -- inv : Domain → Domain
  -- inv f = filter(?) (yx ↦ ∃ₗ(x ↦ ∃ₗ(y ↦ ((x , y) ∈ f) ∧ (yx ≡ (y , x)))))

  module Cardinality where
    -- Injection
    _≼_ : Domain → Domain → Formula
    _≼_ (a)(b) = ∃ₛ(a →ₛₑₜ b)(Injective')

    -- Surjection
    _≽_ : Domain → Domain → Formula
    _≽_ (a)(b) = ∃ₛ(a →ₛₑₜ b)(Surjective'(b))

    -- Bijection
    _≍_ : Domain → Domain → Formula
    _≍_ (a)(b) = ∃ₛ(a →ₛₑₜ b)(Bijective'(b))

    -- Strict injection
    _≺_ : Domain → Domain → Formula
    _≺_ A B = (A ≼ B) ∧ ¬(A ≍ B)

    -- Strict surjection
    _≻_ : Domain → Domain → Formula
    _≻_ A B = (A ≽ B) ∧ ¬(A ≍ B)

    -- TODO: Definition of a "cardinality object" requires ordinals, which requires axiom of choice
    -- # : Domain → Domain

module Structure where
  -- Structures in meta-functions.
  module Function' where -- TODO: Temporary naming fix with tick
    module Properties ⦃ signature : Signature ⦄ where
      open Function renaming (Type to Metatype)

      Type : Domain → Domain → Function → Formula
      Type(X)(Y)(f) = ∀ₛ(X)(x ↦ f(x) ∈ Y)

      Closed : Domain → Function → Formula
      Closed(S)(f) = Type(S)(S)(f)

      Injective'' : Domain → Function → Formula
      Injective''(A)(f) = ∀ₛ(A)(x ↦ ∀ₛ(A)(y ↦ (f(x) ≡ f(y)) ⟶ (x ≡ y)))

      Surjective'' : Domain → Domain → Function → Formula
      Surjective''(A)(B)(f) = ∀ₛ(B)(y ↦ ∃ₛ(A)(x ↦ f(x) ≡ y))

      Bijective'' : Domain → Domain → Function → Formula
      Bijective''(A)(B)(f) =
        Injective''(A)(f)
        ∧ Surjective''(A)(B)(f)

      Preserving₁'' : Domain → Function → Function → Function → Formula
      Preserving₁''(A)(f)(g₁)(g₂) = ∀ₛ(A)(x ↦ f(g₁(x)) ≡ g₂(f(x)))

      Preserving₂'' : Domain → Domain → Function → BinaryOperator → BinaryOperator → Formula
      Preserving₂''(A)(B)(f)(_▫₁_)(_▫₂_) = ∀ₛ(A)(x ↦ ∀ₛ(B)(y ↦ f(x ▫₁ y) ≡ (f(x) ▫₂ f(y))))

  module Relator where
    module Properties where
      Reflexivity : Domain → BinaryRelator → Formula
      Reflexivity(S)(_▫_) = ∀ₛ(S)(x ↦ x ▫ x)

      Irreflexivity : Domain → BinaryRelator → Formula
      Irreflexivity(S)(_▫_) = ∀ₛ(S)(x ↦ ¬(x ▫ x))

      Symmetry : Domain → BinaryRelator → Formula
      Symmetry(S)(_▫_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ (x ▫ y) ⟶ (y ▫ x)))

      Asymmetry : Domain → BinaryRelator → Formula
      Asymmetry(S)(_▫_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ (x ▫ y) ⟶ ¬(y ▫ x)))

      Antisymmetry : Domain → BinaryRelator → Formula
      Antisymmetry(S)(_▫_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ (x ▫ y)∧(y ▫ x) ⟶ (x ≡ y)))

      Transitivity : Domain → BinaryRelator → Formula
      Transitivity(S)(_▫_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ ∀ₛ(S)(z ↦ (x ▫ y)∧(y ▫ z) ⟶ (x ▫ z))))

      Equivalence : Domain → BinaryRelator → Formula
      Equivalence(S)(_▫_) =
        Reflexivity(S)(_▫_)
        ∧ Symmetry(S)(_▫_)
        ∧ Transitivity(S)(_▫_)

      SymmetricallyTotal : Domain → BinaryRelator → Formula
      SymmetricallyTotal(S)(_▫_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ (x ▫ y) ∨ (y ▫ x)))

  module Ordering where
    open Relator.Properties

    Minima : Domain → BinaryRelator → Domain → Formula
    Minima(S)(_≤_)(min) = ∀ₛ(S)(x ↦ min ≤ x)

    Maxima : Domain → BinaryRelator → Domain → Formula
    Maxima(S)(_≤_)(max) = ∀ₛ(S)(x ↦ x ≤ max)

    module _  ⦃ signature : Signature ⦄ where
      open Signature ⦃ ... ⦄

      lowerBounds : Domain → BinaryRelator → Domain → Domain
      lowerBounds(S)(_≤_)(Sₛ) = filter(S)(Minima(S)(_≤_))

      upperBounds : Domain → BinaryRelator → Domain → Domain
      upperBounds(S)(_≤_)(Sₛ) = filter(S)(Maxima(S)(_≤_))

      interval : Domain → BinaryRelator → Domain → Domain → Domain
      interval(S)(_≤_) (a)(b) = filter(S)(s ↦ (a ≤ s) ∧ (s ≤ b))

      Bounded : Domain → BinaryRelator → Domain → Domain → Formula
      Bounded(S)(_≤_) (a)(b) = ∀ₛ(S)(s ↦ (a ≤ s) ∧ (s ≤ b))

      Infima : Domain → BinaryRelator → Domain → Domain → Formula
      Infima(S)(_≤_)(Sₛ)(inf) = Maxima(lowerBounds(S)(_≤_)(Sₛ))(_≤_)(inf)

      Suprema : Domain → BinaryRelator → Domain → Domain → Formula
      Suprema(S)(_≤_)(Sₛ)(sup) = Minima(upperBounds(S)(_≤_)(Sₛ))(_≤_)(sup)

    module Weak where
      PartialOrder : Domain → BinaryRelator → Formula
      PartialOrder(S)(_≤_) =
        Reflexivity(S)(_≤_)
        ∧ Antisymmetry(S)(_≤_)
        ∧ Transitivity(S)(_≤_)

      TotalOrder : Domain → BinaryRelator → Formula
      TotalOrder(S)(_≤_) =
        PartialOrder(S)(_≤_)
        ∧ SymmetricallyTotal(S)(_≤_)

    module Strict where
      Order : Domain → BinaryRelator → Formula
      Order(S)(_<_) =
        Irreflexivity(S)(_<_)
        ∧ Asymmetry(S)(_<_)
        ∧ Transitivity(S)(_<_)

      Dense : Domain → BinaryRelator → Formula
      Dense(S)(_<_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ (x < y) ⟶ ∃ₛ(S)(z ↦ (x < z)∧(z < y))))

  module Operator where
    module Properties where
      AssociativityPattern : Domain → Domain → Domain → BinaryOperator → BinaryOperator → BinaryOperator → BinaryOperator → Formula
      AssociativityPattern(x)(y)(z)(_▫₁_)(_▫₂_)(_▫₃_)(_▫₄_) = (((x ▫₁ y) ▫₂ z) ≡ (x ▫₃ (y ▫₄ z)))

      DistributivityₗPattern : Domain → Domain → Domain → BinaryOperator → BinaryOperator → BinaryOperator → BinaryOperator → BinaryOperator → Formula
      DistributivityₗPattern(x)(y)(z)(_▫₁_)(_▫₂_)(_▫₃_)(_▫₄_)(_▫₅_) = (x ▫₁ (y ▫₂ z)) ≡ ((x ▫₃ y) ▫₄ (x ▫₅ z))

      DistributivityᵣPattern : Domain → Domain → Domain → BinaryOperator → BinaryOperator → BinaryOperator → BinaryOperator → BinaryOperator → Formula
      DistributivityᵣPattern(x)(y)(z)(_▫₁_)(_▫₂_)(_▫₃_)(_▫₄_)(_▫₅_) = ((x ▫₂ y) ▫₁ z) ≡ ((x ▫₃ z) ▫₄  (y ▫₅ z))

      Type : BinaryOperator → Domain → Domain → Domain → Formula
      Type(_▫_)(X)(Y)(Z) = ∀ₛ(X)(x ↦ ∀ₛ(Y)(y ↦ (x ▫ y) ∈ Z))

      Closed : Domain → BinaryOperator → Formula
      Closed(S)(_▫_) = Type(_▫_)(S)(S)(S)

      Commutativity : Domain → BinaryOperator → Formula
      Commutativity(S)(_▫_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ (x ▫ y) ≡ (y ▫ x)))

      Associativity : Domain → BinaryOperator → Formula
      Associativity(S)(_▫_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ ∀ₛ(S)(z ↦ AssociativityPattern(x)(y)(z)(_▫_)(_▫_)(_▫_)(_▫_))))

      Identityₗ : Domain → BinaryOperator → Domain → Formula
      Identityₗ(S)(_▫_)(id) = ∀ₛ(S)(x ↦ (id ▫ x) ≡ x)

      Identityᵣ : Domain → BinaryOperator → Domain → Formula
      Identityᵣ(S)(_▫_)(id) = ∀ₛ(S)(x ↦ (x ▫ id) ≡ x)

      Identity : Domain → BinaryOperator → Domain → Formula
      Identity(S)(_▫_)(id) = Identityₗ(S)(_▫_)(id) ∧ Identityᵣ(S)(_▫_)(id)

      Invertibleₗ : Domain → BinaryOperator → Domain → Formula
      Invertibleₗ(S)(_▫_)(id) = ∀ₛ(S)(x ↦ ∃ₛ(S)(x⁻¹ ↦ (x⁻¹ ▫ x) ≡ id))

      Invertibleᵣ : Domain → BinaryOperator → Domain → Formula
      Invertibleᵣ(S)(_▫_)(id) = ∀ₛ(S)(x ↦ ∃ₛ(S)(x⁻¹ ↦ (x ▫ x⁻¹) ≡ id))

      Invertible : Domain → BinaryOperator → Domain → Formula
      Invertible(S)(_▫_)(id) = ∀ₛ(S)(x ↦ ∃ₛ(S)(x⁻¹ ↦ ((x⁻¹ ▫ x) ≡ id) ∧ ((x ▫ x⁻¹) ≡ id)))

      Distributivityₗ : Domain → BinaryOperator → BinaryOperator → Formula
      Distributivityₗ(S)(_▫₁_)(_▫₂_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ ∀ₛ(S)(z ↦ DistributivityₗPattern(x)(y)(z)(_▫₁_)(_▫₂_)(_▫₁_)(_▫₂_)(_▫₁_))))

      Distributivityᵣ : Domain → BinaryOperator → BinaryOperator → Formula
      Distributivityᵣ(S)(_▫₁_)(_▫₂_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ ∀ₛ(S)(z ↦ DistributivityᵣPattern(x)(y)(z)(_▫₁_)(_▫₂_)(_▫₁_)(_▫₂_)(_▫₁_))))

      Distributivity : Domain → BinaryOperator → BinaryOperator → Formula
      Distributivity(S)(_▫₁_)(_▫₂_) = Distributivityₗ(S)(_▫₁_)(_▫₂_) ∧ Distributivityᵣ(S)(_▫₁_)(_▫₂_)

      Compatibility : Domain → Domain → BinaryOperator → BinaryOperator → Formula
      Compatibility(A)(B)(_▫₁_)(_▫₂_) = ∀ₛ(A)(a₁ ↦ ∀ₛ(A)(a₂ ↦ ∀ₛ(B)(b ↦ AssociativityPattern(a₁)(a₂)(b)(_▫₁_)(_▫₁_)(_▫₂_)(_▫₁_))))

      Semigroup : Domain → BinaryOperator → Formula
      Semigroup(S)(_▫_) =
        Closed(S)(_▫_)
        ∧ Associativity(S)(_▫_)

      Monoid : Domain → BinaryOperator → Formula
      Monoid(S)(_▫_) =
        Semigroup(S)(_▫_)
        ∧ ∃ₛ(S)(Identity(S)(_▫_))

      Group : Domain → BinaryOperator → Formula
      Group(S)(_▫_) =
        Monoid(S)(_▫_)
        ∧ ∀ₛ(S)(id ↦ Identity(S)(_▫_)(id) ⟶ Invertible(S)(_▫_)(id))

      CommutativeGroup : Domain → BinaryOperator → Formula
      CommutativeGroup(S)(_▫_) =
        Group(S)(_▫_)
        ∧ Commutativity(S)(_▫_)

      Rng : Domain → BinaryOperator → BinaryOperator → Formula
      Rng(S)(_▫₁_)(_▫₂_) =
        CommutativeGroup(S)(_▫₁_)
        ∧ Semigroup(S)(_▫₂_)
        ∧ Distributivity(S)(_▫₂_)(_▫₁_)

      Ring : Domain → BinaryOperator → BinaryOperator → Formula
      Ring(S)(_▫₁_)(_▫₂_) =
        CommutativeGroup(S)(_▫₁_)
        ∧ Monoid(S)(_▫₂_)
        ∧ Distributivity(S)(_▫₂_)(_▫₁_)

      module _  ⦃ signature : Signature ⦄ where
        open Signature ⦃ ... ⦄

        Field : Domain → BinaryOperator → BinaryOperator → Formula
        Field(S)(_▫₁_)(_▫₂_) =
          CommutativeGroup(S)(_▫₁_)
          ∧ ∀ₛ(S)(id₁ ↦ Identity(S)(_▫₁_)(id₁) ⟶ CommutativeGroup(S ∖ singleton(id₁))(_▫₂_))
          ∧ Distributivity(S)(_▫₂_)(_▫₁_)

        VectorSpace : Domain → Domain → BinaryOperator → BinaryOperator → BinaryOperator → BinaryOperator → Formula
        VectorSpace(V)(S)(_+ᵥ_)(_⋅ₛᵥ_)(_+ₛ_)(_⋅ₛ_) =
          CommutativeGroup(V)(_+ᵥ_)
          ∧ Field(S)(_+ₛ_)(_⋅ₛ_)
          ∧ ∀ₛ(S)(id ↦ Identity(S)(_⋅ₛ_)(id) ⟶ Identityₗ(V)(_⋅ₛᵥ_)(id))
          ∧ Compatibility(S)(V)(_⋅ₛᵥ_)(_⋅ₛ_)
          ∧ ∀ₛ(S)(s ↦ ∀ₛ(V)(v₁ ↦ ∀ₛ(V)(v₂ ↦ DistributivityₗPattern(s)(v₁)(v₂)(_⋅ₛᵥ_)(_+ᵥ_)(_⋅ₛᵥ_)(_+ᵥ_)(_⋅ₛᵥ_))))
          ∧ ∀ₛ(S)(s₁ ↦ ∀ₛ(S)(s₂ ↦ ∀ₛ(V)(v ↦ DistributivityᵣPattern(s₁)(s₂)(v)(_⋅ₛᵥ_)(_+ᵥ_)(_⋅ₛᵥ_)(_+ᵥ_)(_⋅ₛᵥ_))))

  module Numeral where
    module Natural ⦃ signature : Signature ⦄ where
      open Signature ⦃ ... ⦄

      FormulaInduction : Domain → Domain → Function → (Domain → Formula) → Formula
      FormulaInduction(ℕ)(𝟎)(𝐒) (φ) = (φ(𝟎) ∧ ∀ₛ(ℕ)(n ↦ φ(n) ⟶ φ(𝐒(n)))) ⟶ ∀ₛ(ℕ)(φ)

      SetInduction : Domain → Domain → Function → Formula
      SetInduction(ℕ)(𝟎)(𝐒) = ∀ₗ(X ↦ ((𝟎 ∈ X) ∧ ∀ₛ(ℕ)(n ↦ (n ∈ X) ⟶ (𝐒(n) ∈ X))) ⟶ (ℕ ⊆ X))
      -- TODO: Can be expressed as ∀ₗ(X ↦ Inductive(X) ⟶ (ℕ ⊆ X))

      -- A set ℕ which can be constructed ℕ-inductively.
      Peano : Domain → Domain → Function → Formula
      Peano(ℕ)(𝟎)(𝐒) =
        (𝟎 ∈ ℕ)
        ∧ Function'.Properties.Closed(ℕ)(𝐒)
        ∧ Function'.Properties.Injective''(ℕ)(𝐒)
        ∧ ∀ₛ(ℕ)(n ↦ 𝐒(n) ≢ 𝟎)
        ∧ SetInduction(ℕ)(𝟎)(𝐒)

-- A model of natural numbers expressed in set theory (using only sets).
module NumeralNatural ⦃ signature : Signature ⦄ where
  open Signature ⦃ ... ⦄
  open FunctionSet.Cardinality

  -- The zero constant from the standard inductive set definition of ℕ in ZFC set theory.
  𝟎 : Domain
  𝟎 = ∅

  -- The successor function from the standard inductive set definition of ℕ in ZFC set theory.
  -- This means that all lesser numbers are contained in every number.
  -- Examples:
  -- • 0: {}
  -- • 1: 0∪{0} = {0} = {{},{{}}}
  -- • 2: 1∪{1} = {0}∪{1} = {0,1} = {{},{{},{{}}}}
  -- • 3: 2∪{2} = {0,1}∪{2} = {0,1,2} = {{{},{{},{{}}}},{{{},{{},{{}}}}}}
  -- • 4: 3∪{3} = {0,1,2}∪{3} = {0,1,2,3} = {{{{},{{},{{}}}},{{{},{{},{{}}}}}},{{{{},{{},{{}}}},{{{},{{},{{}}}}}}}}
  𝐒 : Domain → Domain
  𝐒(n) = n ∪ singleton(n)

  -- A set is ℕ-inductive when has zero and all its successors.
  -- In loose terms: Inductive(I) means (I ⊆ ℕ)
  Inductive : Domain → Formula
  Inductive(I) = (𝟎 ∈ I) ∧ (∀ₗ(x ↦ (x ∈ I) ⟶ (𝐒(x) ∈ I)))

  -- The "smallest" inductive set is the set of natural numbers.
  -- All elements which can be expressed using only 𝟎 and 𝐒.
  ℕ : Domain
  ℕ = ⋂(filter(℘(inductiveSet)) Inductive) -- TODO: This pattern seems useful

  -- The relation "lesser than" in this model of ℕ.
  -- This works for all elements in ℕ by the definition of 𝟎 and 𝐒.
  _<_ : BinaryRelator
  a < b = a ∈ b

  _≤_ : BinaryRelator
  a ≤ b = (a < b) ∨ (a ≡ b)

  _>_ : BinaryRelator
  a > b = b < a

  _≥_ : BinaryRelator
  a ≥ b = b ≤ a

  infixl 2000 _<_ _≤_ _>_ _≥_

  𝕟 : Domain → Domain
  𝕟(n) = filter(ℕ) (_< n)

  Finite : Domain → Formula
  Finite(s) = ∃ₛ(ℕ)(n ↦ s ≼ 𝕟(n)) -- TODO: Now this means that there is an injection (s → 𝕟(n)), which is equivalent to the existance of an surjection (𝕟(n) → s) because stuff that follows from excluded middle (more specifically ((s ≼ 𝕟(n)) ↔ (𝕟(n) ≽ s))). Define ∑ (summation over finite sets) by using the existance of a finite sequence

-- A model of integers expressed in set theory (using only sets).
module NumeralInteger ⦃ signature : Signature ⦄ where
  open NumeralNatural

  -- a

module Axioms ⦃ signature : Signature ⦄ where
  open NumeralNatural using () renaming (Inductive to [ℕ]-Inductive)
  open Function ⦃ ... ⦄
  open FunctionSet ⦃ ... ⦄
  open Signature ⦃ ... ⦄

  -- A set which is empty exists.
  -- • Allows a construction of the empty set.
  EmptySetInclusion : Formula
  EmptySetInclusion = Empty(∅)

  -- A set with two elements exists.
  -- • Allows a construction of a set with two elements.
  PairingInclusion : Formula
  PairingInclusion = ∀ₗ(x₁ ↦ ∀ₗ(x₂ ↦ (∀ₗ(x ↦ (x ∈ pair(x₁)(x₂)) ⟷ (x ≡ x₁)∨(x ≡ x₂)))))

  -- A set which is the subset of a set where all elements satisfies a predicate exists.
  RestrictedComprehension : (Domain → Formula) → Formula
  RestrictedComprehension(φ) = ∀ₗ(s ↦ ∀ₗ(x ↦ ((x ∈ filter(s)(φ)) ⟷ ((x ∈ s) ∧ φ(x)))))

  -- A set which contains all the subsets of a set exists.
  -- • Allows a construction of a set that is the powerset of a set.
  PowerSetInclusion : Formula
  PowerSetInclusion = ∀ₗ(s ↦ ∀ₗ(x ↦ (x ∈ ℘(s)) ⟷ (x ⊆ s)))

  -- A set which contains all the elements of a group of sets exists.
  -- • Allows a construction of a set that is the union of some sets.
  UnionInclusion : Formula
  UnionInclusion = ∀ₗ(ss ↦ ∀ₗ(x ↦ (x ∈ ⋃(ss)) ⟷ ∃ₗ(s ↦ (s ∈ ss)∧(x ∈ s))))

  -- A ℕ-inductive set exists.
  -- • An inductive set is infinite, so this implies that an infinite set exists.
  -- • Makes it possible to construct the set of natural numbers (ℕ).
  Infinity : Formula
  Infinity = [ℕ]-Inductive(inductiveSet)

  -- Set equality is determined by its contents.
  -- • Guarantees the definition of equality for sets.
  Extensionality : Formula
  Extensionality = ∀ₗ(s₁ ↦ ∀ₗ(s₂ ↦ ∀ₗ(x ↦ (x ∈ s₁)⟷(x ∈ s₂)) ⟷ (s₁ ≡ s₂)))

  -- A non-empty set contain sets that are disjoint to it.
  -- • Prevents sets containing themselves.
  -- • Making every set have an ordinal rank.
  Regularity : Formula
  Regularity = ∀ₗ(s₁ ↦ (NonEmpty(s₁) ⟶ ∃ₗ(s₂ ↦ (s₂ ∈ s₁) ∧ Disjoint(s₁)(s₂))))

  -- The `map`-function on sets yields/returns sets.
  -- • The `map`-function on a function is a function from sets to sets.
  Replacement : (Domain → Domain) → Formula
  Replacement(f) = ∀ₗ(A ↦ ∀ₗ(y ↦ (y ∈ map f(A)) ⟷ (∃ₛ(A)(x ↦ y ≡ f(x)))))
  -- ReplacementTraditional = ∀{φ : Domain → Domain → Formula} → Proof(∀ₗ(A ↦ TotalFunction(φ)(A) ⟶ ∃ₗ(B ↦ ∀ₗ(y ↦ (y ∈ B) ⟷ ∃ₗ(x ↦ (x ∈ A) ∧ φ(x)(y))))))

  -- The set product of non-empty finite indexed family of sets where all the sets are non-empty is non-empty.
  -- TODO: Should the indexed family really be finite? https://en.wikipedia.org/wiki/Cartesian_product#Infinite_Cartesian_products
  -- Choice = ∀{n : Meta.ℕ}{F : FiniteIndexedFamily(Meta.𝐒(n))} → (∀{i : Meta.𝕟(Meta.𝐒(n))} → Proof(NonEmpty(F(i)))) → Proof(NonEmpty(∏ F))
  Choice : (Domain → Domain) → Formula
  Choice(f) = ∀ₗ(y ↦ (Value f(y)) ⟶ ((f ∘ (inv f))(y) ≡ y))
  -- ChoiceTraditional = Proof(∀ₗ(s ↦ (∅ ∉ s) ⟶ ∃ₛ(s →ₛₑₜ (⋃ s))(f ↦ ∀ₛ(s)(x ↦ ∀ₛ(⋃ s)(y ↦ ((x , y) ∈ f) ⟶ (y ∈ x))))))

record Z ⦃ signature : Signature ⦄ : Set((ℓₗ Lvl.⊔ ℓₒ) Lvl.⊔ ℓₘₗ) where
  open Axioms
  open Signature ⦃ ... ⦄

  field
    extensional   : Proof(Extensionality)
    empty         : Proof(EmptySetInclusion)
    pairing       : Proof(PairingInclusion)
    comprehension : ∀{φ} → Proof(RestrictedComprehension(φ))
    union         : Proof(UnionInclusion)
    power         : Proof(PowerSetInclusion)
    infinity      : Proof(Infinity)

record ZF ⦃ signature : Signature ⦄ : Set((ℓₗ Lvl.⊔ ℓₒ) Lvl.⊔ ℓₘₗ) where
  open Axioms
  open Signature ⦃ ... ⦄

  field
    extensional   : Proof(Extensionality)
    empty         : Proof(EmptySetInclusion)
    pairing       : Proof(PairingInclusion)
    comprehension : ∀{φ} → Proof(RestrictedComprehension(φ))
    union         : Proof(UnionInclusion)
    power         : Proof(PowerSetInclusion)
    infinity      : Proof(Infinity)
    regular       : Proof(Regularity)
    replacement   : ∀{f} → Proof(Replacement(f))

record ZFC ⦃ signature : Signature ⦄ : Set((ℓₗ Lvl.⊔ ℓₒ) Lvl.⊔ ℓₘₗ) where
  open Axioms
  open Signature ⦃ ... ⦄

  field
    extensional   : Proof(Extensionality)
    empty         : Proof(EmptySetInclusion)
    pairing       : Proof(PairingInclusion)
    comprehension : ∀{φ} → Proof(RestrictedComprehension(φ))
    union         : Proof(UnionInclusion)
    power         : Proof(PowerSetInclusion)
    infinity      : Proof(Infinity)
    regular       : Proof(Regularity)
    replacement   : ∀{f} → Proof(Replacement(f))
    choice        : ∀{f} → Proof(Choice(f))

module Proofs ⦃ signature : Signature ⦄ ⦃ axioms : ZF ⦄ where
  open Axioms
  open Signature ⦃ ... ⦄
  open ZF ⦃ ... ⦄

  open SetEquality ⦃ ... ⦄        hiding (extensional)
  open SingletonSet ⦃ ... ⦄       hiding (singleton)
  open FilterSet ⦃ ... ⦄          hiding (filter)
  open PowerSet ⦃ ... ⦄           hiding (℘)
  open SetUnionSet ⦃ ... ⦄        hiding (⋃)
  open UnionSet ⦃ ... ⦄           hiding (_∪_)
  open IntersectionSet ⦃ ... ⦄    hiding (_∩_)
  open WithoutSet ⦃ ... ⦄         hiding (_∖_)
  open SetIntersectionSet ⦃ ... ⦄ hiding (⋂)

  -- All sets are either empty or non-empty.
  postulate Empty-excluded-middle : ∀{s} → Proof(Empty(s) ∨ NonEmpty(s))

  pair-inclusion : Proof(∀ₗ(a₁ ↦ ∀ₗ(a₂ ↦ (∀ₗ(x ↦ (x ∈ pair(a₁)(a₂)) ⟷ (x ≡ a₁)∨(x ≡ a₂))))))
  pair-inclusion = pairing

  instance
    setEqualityInstance : SetEquality
    setEqualityInstance = SetEquality.intro extensional

  instance
    emptySetInstance : EmptySet
    emptySetInstance = EmptySet.intro ∅ empty

  instance
    singletonSetInstance : SingletonSet
    singletonSetInstance = SingletonSet.intro singleton
      ([∀].intro (\{a} →
        ([∀].intro (\{x} →
          [↔].transitivity
            ([∀].elim([∀].elim([∀].elim(pair-inclusion){a}){a}){x})
            ([↔].intro ([∨].redundancyₗ) ([∨].redundancyᵣ))
        ))
      ))

  instance
    filterSetInstance : FilterSet
    filterSetInstance = FilterSet.intro filter comprehension

  instance
    powerSetInstance : PowerSet
    powerSetInstance = PowerSet.intro ℘ power

  instance
    setUnionSetInstance : SetUnionSet
    setUnionSetInstance = SetUnionSet.intro ⋃ union

  instance
    unionSetInstance : UnionSet
    unionSetInstance = UnionSet.intro _∪_
      ([∀].intro (\{a} →
        ([∀].intro (\{b} →
          ([∀].intro (\{x} →
            ([∀].elim([∀].elim [⋃]-inclusion{pair(a)(b)}){x})
            〔ₗ [↔].transitivity 〕
            ([↔]-with-[∃] (\{s} →
              ([↔]-with-[∧]ₗ ([∀].elim([∀].elim([∀].elim pair-inclusion{a}){b}){s}))
              〔ₗ [↔].transitivity 〕
              ([∧][∨]-distributivityᵣ)
              〔ₗ [↔].transitivity 〕
              [↔]-with-[∨] ([≡]-substitute-this-is-almost-trivial) ([≡]-substitute-this-is-almost-trivial)
            ))
            〔ₗ [↔].transitivity 〕
            ([↔].intro ([∃]-redundancyₗ) ([∃]-redundancyᵣ))
          ))
        ))
      ))

  instance
    intersectionSetInstance : IntersectionSet
    intersectionSetInstance = IntersectionSet.intro _∩_
      ([∀].intro (\{a} →
        ([∀].intro (\{b} →
          ([∀].elim(filter-inclusion){a})
        ))
      ))

  instance
    withoutSetInstance : WithoutSet
    withoutSetInstance = WithoutSet.intro _∖_
      ([∀].intro (\{a} →
        ([∀].intro (\{b} →
          ([∀].elim(filter-inclusion){a})
        ))
      ))

  instance
    setIntersectionSetInstance : SetIntersectionSet
    setIntersectionSetInstance = SetIntersectionSet.intro ⋂
      ([∀].intro (\{ss} →
        ([∀].intro (\{x} →
          ([↔].intro
            -- (⟵)-case
            (allssinssxins ↦
              ([↔].elimₗ
                ([∀].elim([∀].elim filter-inclusion{⋃(ss)}){x})
                ([∧].intro
                  -- x ∈ ⋃(ss)
                  ([∨].elim
                    -- Empty(ss) ⇒ _
                    (allyyninss ↦
                      proof -- TODO: But: Empty(ss) ⇒ (ss ≡ ∅) ⇒ ⋃(ss) ≡ ∅ ⇒ (x ∉ ⋃(ss)) ? Maybe use this argument further up instead to prove something like: (⋂(ss) ≡ ∅) ⇒ (x ∉ ∅)
                    )

                    -- NonEmpty(ss) ⇒ _
                    (existsyinss ↦
                      ([∃].elim
                        (\{y} → yinss ↦ (
                          ([↔].elimₗ([∀].elim([∀].elim([⋃]-inclusion){ss}){x}))
                          ([∃].intro{_}
                            {y}
                            ([∧].intro
                              -- y ∈ ss
                              (yinss)

                              -- x ∈ y
                              ([→].elim
                                ([∀].elim(allssinssxins){y})
                                (yinss)
                              )
                            )
                          )
                        ))
                        (existsyinss)
                      )
                    )
                    (Empty-excluded-middle{ss})
                  )

                  -- ∀(s∊ss). x∈s
                  (allssinssxins)
                )
              )
            )

            -- (⟶)-case
            (xinintersectss ↦
              ([∀].intro (\{s} →
                ([→].intro (sinss ↦
                  ([→].elim
                    ([∀].elim
                      ([∧].elimᵣ
                        ([↔].elimᵣ
                          ([∀].elim
                            ([∀].elim
                              filter-inclusion
                              {⋃(ss)}
                            )
                            {x}
                          )
                          (xinintersectss)
                        )
                      )
                      {s}
                    )
                    (sinss)
                  )
                ))
              ))
            )
          )
        ))
      ))
      where postulate proof : ∀{a} → a

  -- postulate any : ∀{l}{a : Set(l)} → a

  -- TODO: Just used for reference. Remove these lines later
  -- ⋂(a) = filter(⋃(ss)) (x ↦ ∀ₗ(a₂ ↦ (a₂ ∈ ss) ⟶ (x ∈ a₂)))
  -- filter-inclusion : ∀{φ : Domain → Formula} → Proof(∀ₗ(s ↦ ∀ₗ(x ↦ ((x ∈ filter(s)(φ)) ⟷ ((x ∈ s) ∧ φ(x))))))
  -- [⋃]-inclusion : Proof(∀ₗ(ss ↦ ∀ₗ(x ↦ (x ∈ ⋃(ss)) ⟷ ∃ₗ(s ↦ (s ∈ ss)∧(x ∈ s)))))


  -- [⨯]-inclusion : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(x ↦ (x ∈ (a ⨯ b)) ⟷ ∃ₛ(a)(x₁ ↦ ∃ₛ(b)(x₂ ↦ x ≡ (x₁ , x₂)))))))
  -- [⨯]-inclusion =

  -- [⋃][℘]-inverse : Proof(∀ₗ(s ↦ ⋃(℘(s)) ≡ s))

  module FunctionProofs where
    open Function ⦃ signature ⦄
    open FunctionSet ⦃ signature ⦄

    [∃]-unrelatedᵣ-[→]ᵣ-inside-[∀ₛ] : ∀{D : Domain}{P : BinaryRelator} → Proof(∀ₗ(x ↦ ∃ₗ(y ↦ (x ∈ D) ⟶ P(x)(y))) ⟷ ∀ₛ(D)(x ↦ ∃ₗ(y ↦ P(x)(y))))
    [∃]-unrelatedᵣ-[→]ᵣ-inside-[∀ₛ] {D}{P} = [↔]-with-[∀] ([∃]-unrelatedᵣ-[→])

    [∀ₛ∃!]-to[∀ₛ∃] : ∀{P : BinaryRelator}{D : Domain} → Proof(∀ₛ(D)(x ↦ ∃ₗ!(y ↦ P(x)(y)))) → Proof(∀ₛ(D)(x ↦ ∃ₗ(y ↦ P(x)(y))))
    [∀ₛ∃!]-to[∀ₛ∃] proof =
      ([∀ₛ]-intro(\{x} → xinD ↦
        [∧].elimₗ([∀ₛ]-elim proof {x} xinD)
      ))

    -- The construction of a meta-function in the meta-logic from a function in the set theory
    fnset-witness : ∀{D} → (f : Domain) → ⦃ _ : Proof(Total(D)(f)) ⦄ → Function
    fnset-witness f ⦃ proof ⦄ = [∃]-fn-witness ⦃ [↔].elimₗ [∃]-unrelatedᵣ-[→]ᵣ-inside-[∀ₛ] (proof) ⦄

    fnset-value : ∀{D} → (f : Domain) → ⦃ proof : Proof(Total(D)(f)) ⦄ → Proof(∀ₛ(D)(x ↦ (x , fnset-witness f(x)) ∈ f))
    fnset-value{D} f ⦃ proof ⦄ = [∃]-fn-proof ⦃ [↔].elimₗ [∃]-unrelatedᵣ-[→]ᵣ-inside-[∀ₛ] (proof) ⦄

    fnset-proof : ∀{D} → (f : Domain) → ⦃ _ : Proof(FunctionSet(f)) ⦄ → ⦃ total : Proof(Total(D)(f)) ⦄ → Proof(∀ₛ(D)(x ↦ ∀ₗ(y ↦ (fnset-witness{D} f ⦃ total ⦄ x ≡ y) ⟷ ((x , y) ∈ f))))
    fnset-proof{D} f ⦃ function ⦄ ⦃ total ⦄ =
      ([∀ₛ]-intro(\{x} → x∈D ↦
        ([∀].intro(\{y} →
          ([↔].intro
            (xy∈f ↦
              ([→].elim
                ([∀].elim([∀].elim([∀].elim function{x}) {fnset-witness f(x)}) {y})
                ([∧].intro
                  ([∀ₛ]-elim(fnset-value f) {x} (x∈D))
                  (xy∈f)
                )
              )
            )

            (fx≡y ↦
              [≡].elimᵣ (fx≡y) ([∀ₛ]-elim (fnset-value(f)) {x} (x∈D))
            )
          )
        ))
      ))

    [→ₛₑₜ]-witness : ∀{A B} → (f : Domain) → ⦃ _ : Proof(f ∈ (A →ₛₑₜ B)) ⦄ → Function
    [→ₛₑₜ]-witness f ⦃ proof ⦄ (x) =
      (fnset-witness f
        ⦃ [∧].elimᵣ([∧].elimᵣ([↔].elimᵣ
          ([∀].elim([∀].elim filter-inclusion))
          (proof)
        )) ⦄
        (x)
      )

  module NumeralNaturalProofs where
    open NumeralNatural
    open Structure
    open Structure.Function'.Properties
    open Structure.Relator
    open Structure.Relator.Properties

    [∩]-inductive : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ (Inductive(a) ∧ Inductive(b)) ⟶ Inductive(a ∩ b))))
    [∩]-inductive =
      ([∀].intro (\{a} →
        ([∀].intro (\{b} →
          ([→].intro(indaindb ↦
            ([∧].intro
              -- ∅ is in
              ([↔].elimₗ
                ([∀].elim([∀].elim([∀].elim([∩]-inclusion){a}){b}){∅})
                ([∧].intro
                  ([∧].elimₗ([∧].elimₗ indaindb))
                  ([∧].elimₗ([∧].elimᵣ indaindb))
                )
              )

              -- 𝐒 is in
              ([∀].intro (\{x} →
                ([→].intro(x∈a∩b ↦
                  ([↔].elimₗ
                    ([∀].elim([∀].elim([∀].elim([∩]-inclusion){a}){b}){𝐒(x)})
                    ([∧].intro
                      -- 𝐒(x) ∈ a
                      ([→].elim([∀].elim([∧].elimᵣ([∧].elimₗ indaindb)){x})(
                        -- x ∈ a
                        [∧].elimₗ([↔].elimᵣ
                          ([∀].elim([∀].elim([∀].elim([∩]-inclusion){a}){b}){x})
                          (x∈a∩b)
                        )
                      ))

                      -- 𝐒(x) ∈ b
                      ([→].elim([∀].elim([∧].elimᵣ([∧].elimᵣ indaindb)){x})(
                        -- x ∈ b
                        [∧].elimᵣ([↔].elimᵣ
                          ([∀].elim([∀].elim([∀].elim([∩]-inclusion){a}){b}){x})
                          (x∈a∩b)
                        )
                      ))
                    )
                  )
                ))
              ))
            )
          ))
        ))
      ))

    -- postulate [⋂]-property : ∀{φ} → Proof(∀ₗ(s ↦ ∀ₗ(x ↦ (x ∈ s) ⟶ φ(x)) ⟶ φ(⋂ s))) TODO: MAybe not true
    [⋂]-inductive : Proof(∀ₗ(s ↦ ∀ₗ(x ↦ (x ∈ s) ⟶ Inductive(x)) ⟶ Inductive(⋂ s)))
    [⋂]-inductive =
      ([∀].intro (\{s} →
        ([→].intro(allxxsindx ↦
          ([∧].intro
            -- ∅ is in
            proof

            -- 𝐒 is in
            proof
          )
        ))
      ))
      where postulate proof : ∀{a} → a

    [ℕ]-inductive : Proof(Inductive(ℕ))
    [ℕ]-inductive =
      ([→].elim
        ([∀].elim
          [⋂]-inductive
          {filter(℘(inductiveSet)) Inductive}
        )
        ([∀].intro(\{x} →
          ([→].intro(x∈filter ↦
            [∧].elimᵣ(([↔].elimᵣ([∀].elim([∀].elim filter-inclusion{℘(inductiveSet)}){x})) (x∈filter))
          ))
        ))
      )

    module _ where
      open Function
      open FunctionProofs

      {- TODO: Something is amiss here? This should only guarantee the existence of a function when the arguments are in ℕ. The problem is probably that Total may not actually describe a set? See the TODO for Total. Maybe one should use BoundedFunctionSet instead? But Total defines a set by using filter, so maybe it is the unique existence to metaobject function that makes this weird?
      postulate [ℕ]-recursive-function : ∀{z : Domain}{s : Domain → Domain → Domain} → Proof(∃ₛ!(ℕ →ₛₑₜ ℕ)(f ↦ ((𝟎 , z) ∈ f) ∧ (∀ₗ(n ↦ ∀ₗ(fn ↦ ((n , fn) ∈ f) ⟶ ((𝐒(n) , s(n)(fn)) ∈ f))))))

      [ℕ]-recursive-function-witness : Domain → BinaryOperator → Function
      [ℕ]-recursive-function-witness z s = fnset-witness([∃ₛ!]-witness ⦃ f ⦄ ) ⦃ [∀ₛ]-elim ([∀].elim filter-property) ([∃ₛ!]-domain ⦃ f ⦄) ⦄ where
        f = [ℕ]-recursive-function{z}{s}

      _+_ : Domain → Domain → Domain
      _+_ a b = [ℕ]-recursive-function-witness z s b where
        z : Domain
        z = a

        s : Domain → Domain → Domain
        s(n)(sn) = 𝐒(sn)

      _⋅_ : Domain → Domain → Domain
      _⋅_ a b = [ℕ]-recursive-function-witness z s b where
        z : Domain
        z = 𝟎

        s : Domain → Domain → Domain
        s(n)(sn) = sn + a

      _^'_ : Domain → Domain → Domain -- TODO: Temporary name collision fix
      _^'_ a b = [ℕ]-recursive-function-witness z s b where
        z : Domain
        z = 𝐒(𝟎)

        s : Domain → Domain → Domain
        s(n)(sn) = sn ⋅ a
      -}

    postulate [ℕ]-elements : Proof(∀ₛ(ℕ)(n ↦ (n ≡ 𝟎) ∨ ∃ₛ(ℕ)(p ↦ n ≡ 𝐒(p))))

    postulate [<]-irreflexivity : Proof(Irreflexivity(ℕ)(_<_))
    postulate [<]-asymmetry     : Proof(Antisymmetry(ℕ)(_<_))
    postulate [<]-transitivity  : Proof(Transitivity(ℕ)(_<_))

    postulate [≤]-reflexivity  : Proof(Irreflexivity(ℕ)(_≤_))
    postulate [≤]-antisymmetry : Proof(Antisymmetry(ℕ)(_≤_))
    postulate [≤]-transitivity : Proof(Transitivity(ℕ)(_≤_))

    -- instance
    --   [𝐒]-type : Function.Type(𝐒)
    --   [𝐒]-type = Function.Type.intro ℕ ℕ proof where
    --     postulate proof : ∀{a} → a

    -- postulate [𝐒]-injective : Proof(Injective(ℕ)(𝐒))

    -- ∀ₛ(ℕ)(a ↦ ∀ₛ(ℕ)(b ↦ (a < b) ⟶ (𝐒(a) < 𝐒(b))))
    -- ∀ₛ(ℕ)(n ↦ 𝟎 ≢ 𝐒(n))
