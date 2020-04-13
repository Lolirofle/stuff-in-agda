module Structure.Topology where

open import Logic
import      Lvl
open import Sets.ExtensionalPredicateSet renaming (_≡_ to _≡ₛ_)
open import Structure.Setoid
open import Type

private variable ℓ : Lvl.Level

record TopologicalSpace {ℓ₁ ℓ₂ ℓ₃} {X : Type{ℓ₁}} ⦃ equiv : Equiv(X) ⦄ (𝓣 : PredSet{ℓ₂}(PredSet{ℓ₁ ⊔ ℓ₃}(X))) : Type{Lvl.𝐒 ℓ₁ ⊔ ℓ₂ ⊔ Lvl.𝐒 ℓ₃} where
  field
    contains-empty        : (∅ ∈ 𝓣)
    contains-universe     : (𝐔 ∈ 𝓣)
    intersection-closure  : ∀{A B} → (A ∈ 𝓣) → (B ∈ 𝓣) → ((A ∩ B) ∈ 𝓣)
    indexed-union-closure : ∀{I : Type{ℓ₁ ⊔ ℓ₃}}{Ai : I → PredSet{ℓ₁ ⊔ ℓ₃}(X)} → (∀{i} → (Ai(i) ∈ 𝓣)) → ((⋃ᵢ Ai) ∈ 𝓣)

  Open : PredSet{ℓ₁ ⊔ ℓ₃}(X) → Stmt
  Open(A) = (A ∈ 𝓣)

  Closed : PredSet{ℓ₁ ⊔ ℓ₃}(X) → Stmt
  Closed(A) = Open(∁ A)

  record Neighborhood (p : X) (N : PredSet{ℓ₁ ⊔ ℓ₃}(X)) : Stmt{Lvl.𝐒(ℓ₁) ⊔ ℓ₂ ⊔ Lvl.𝐒(ℓ₃)} where
    constructor intro
    field
      O : PredSet{ℓ₁ ⊔ ℓ₃}(X)
      ⦃ open-set ⦄       : Open(O)
      ⦃ covers ⦄         : O ⊆ N
      ⦃ contains-point ⦄ : p ∈ O

  open import Data
  open import Data.Proofs
  open import Data.Either as Either using (_‖_)
  open import Data.Either.Equiv
  open import Data.Boolean
  open import Data.Tuple as Tuple using (_⨯_ ; _,_)
  open import Functional
  open import Lang.Instance
  open import Logic.Propositional
  open import Logic.Predicate
  open import Lvl.Proofs
  import      Relator.Equals.Proofs.Equiv
  open import Structure.Function.Domain
  open import Structure.Function
  open import Structure.Relator.Proofs
  open import Structure.Relator.Properties
  open import Structure.Relator
  open import Syntax.Function
  open import Syntax.Transitivity

  module _ where
    open Relator.Equals.Proofs.Equiv(Bool) renaming ([≡]-equiv to bool-equiv)

    union-closure : ∀{A B} → (A ∈ 𝓣) → (B ∈ 𝓣) → ((A ∪ B) ∈ 𝓣)
    union-closure {A}{B} pa pb = substitute₂(_∋_) (reflexivity(_≡_) {x = 𝓣}) (⋃ᵢ-of-bijection ([∃]-intro Lvl.Up.obj) 🝖 ⋃ᵢ-of-boolean) (indexed-union-closure f-proof) where
      f-proof : ∀{i} → ((if i then B else A) ∈ 𝓣)
      f-proof {𝐹} = pa
      f-proof {𝑇} = pb

  instance
    Neighborhood-unaryRelator : ∀{N} → UnaryRelator(p ↦ Neighborhood p N)
    UnaryRelator.substitution Neighborhood-unaryRelator xy (intro O ⦃ contains-point = p ⦄) = intro O ⦃ contains-point = substitute₁(_∈ O) xy p ⦄

  record Base {I : Type{ℓ₁ ⊔ ℓ₃}} (Bi : I → PredSet{ℓ₁ ⊔ ℓ₃}(X)) : Stmt{Lvl.𝐒(ℓ₁ ⊔ ℓ₃)} where
    constructor intro
    field
      covers-space : (∀{x} → (x ∈ (⋃ᵢ Bi)))
      generator : (x : X) → (i₁ i₂ : I) → ⦃ _ : (x ∈ (Bi(i₁) ∩ Bi(i₂))) ⦄ → I
      generator-contains-point : ∀{x : X}{i₁ i₂ : I} ⦃ _ : x ∈ (Bi(i₁) ∩ Bi(i₂)) ⦄ → (x ∈ Bi(generator x i₁ i₂))
      generator-subset : ∀{x : X}{i₁ i₂ : I} ⦃ _ : x ∈ (Bi(i₁) ∩ Bi(i₂)) ⦄ → (Bi(generator x i₁ i₂) ⊆ (Bi(i₁) ∩ Bi(i₂)))

  record ClosurePoint (A : PredSet{ℓ₁ ⊔ ℓ₃}(X)) (p : X) : Stmt{Lvl.𝐒(ℓ₁) ⊔ ℓ₂ ⊔ Lvl.𝐒(ℓ₃)} where
    constructor intro
    field proof : ∀{N} → ⦃ _ : Neighborhood(p)(N) ⦄ → NonEmpty(A ∩ N)

  instance
    ClosurePoint-unaryRelator : ∀{A} → UnaryRelator(ClosurePoint(A))
    ClosurePoint.proof (UnaryRelator.substitution ClosurePoint-unaryRelator xy Ax) {N} ⦃ neigh-y ⦄ = [∃]-map-proof id (ClosurePoint.proof Ax {N} ⦃ substitute₁ₗ(p ↦ Neighborhood p N) xy neigh-y ⦄)

  InternalPoint = swap Neighborhood

  record LimitPoint (A : PredSet{ℓ₁ ⊔ ℓ₃}(X)) (p : X) : Stmt{Lvl.𝐒(ℓ₁) ⊔ ℓ₂ ⊔ Lvl.𝐒(ℓ₃)} where
    constructor intro
    field proof : ∀{N} → ⦃ _ : Neighborhood(p)(N) ⦄ → NonEmpty(A ∩ (N ∖ (• p)))

  -- TODO: Level problem in PredSet. IsolatedPoint-unaryRelator has the same problem because they both use the singleton construction (•_) which requires a level dependency between elements and sets.
  instance
    postulate LimitPoint-unaryRelator : ∀{A} → UnaryRelator(LimitPoint(A))
    {-LimitPoint.proof (UnaryRelator.substitution (LimitPoint-unaryRelator {A = A}) xy (intro proof)) {N} ⦃ neigh ⦄ = substitute₁(_) xy (proof ⦃ substitute₁ₗ(_) xy neigh ⦄) where
      instance
        inst : UnaryRelator(x ↦ NonEmpty(A ∩ (N ∖ (• x))))
        inst = [∘]-unaryRelator {f = x ↦ A ∩ (N ∖ (• x))} ⦃ {!!} ⦄ {P = NonEmpty} ⦃ {!!} ⦄
    -}

  record IsolatedPoint (A : PredSet{ℓ₁ ⊔ ℓ₃}(X)) (p : X) : Stmt{Lvl.𝐒(ℓ₁) ⊔ ℓ₂ ⊔ Lvl.𝐒(ℓ₃)} where
    constructor intro
    field
      N : PredSet{ℓ₁ ⊔ ℓ₃}(X)
      ⦃ neighborhood ⦄ : Neighborhood(p)(N)
      proof : ((A ∩ N) ≡ₛ (• p))

  -- TODO: Level problem in PredSet
  instance
    postulate IsolatedPoint-unaryRelator : ∀{A} → UnaryRelator(IsolatedPoint(A))
    {-UnaryRelator.substitution IsolatedPoint-unaryRelator xy (intro N p) = intro N ⦃ substitute₁(_) xy infer ⦄ ([≡]-transitivity-raw p {![≡]-with(•_) xy!})
  -}

  Closure : PredSet{ℓ₁ ⊔ ℓ₃}(X) → PredSet(X)
  Closure(A) = ⊷(ClosurePoint(A))

  Interior : PredSet{ℓ₁ ⊔ ℓ₃}(X) → PredSet(X)
  Interior(A) = ⊷(InternalPoint(A))

  ∂ : PredSet{ℓ₁ ⊔ ℓ₃}(X) → PredSet(X)
  ∂ A = Closure(A) ∖ Interior(A)

  Discrete : PredSet{ℓ₁ ⊔ ℓ₃}(X) → Stmt
  Discrete(A) = A ⊆ ⊷(IsolatedPoint(A))

  Dense : PredSet{ℓ₁ ⊔ ℓ₃}(X) → Stmt
  Dense(A) = Closure(A) ⊆ A

  Perfect : PredSet{ℓ₁ ⊔ ℓ₃}(X) → Stmt
  Perfect(A) = ∀{p} → (¬ IsolatedPoint(A)(p))

  open import Numeral.Natural
  open import Numeral.Natural.Relation.Order

  record _converges-to_ (f : ℕ → X) (L : X) : Stmt{Lvl.𝐒(ℓ₁) ⊔ ℓ₂ ⊔ Lvl.𝐒(ℓ₃)} where
    constructor intro
    field
      min : ∃(Neighborhood(L)) → ℕ
      proof : ∀{NN@([∃]-intro N) : ∃(Neighborhood(L))}{n : ℕ} → (n > min(NN)) → (f(n) ∈ N)
  lim : (f : ℕ → X) → ⦃ _ : ∃(f converges-to_) ⦄ → X
  lim f ⦃ [∃]-intro L ⦄ = L

module _
  {ℓₗ₁ ℓₗ₂ ℓₗ₃} {X : Type{ℓₗ₁}} ⦃ equiv : Equiv(X) ⦄ (𝓣ₗ : PredSet{ℓₗ₂}(PredSet{ℓₗ₁ ⊔ ℓₗ₃}(X)))
  ⦃ _ : TopologicalSpace{ℓₗ₁}{ℓₗ₂}{ℓₗ₃} (𝓣ₗ) ⦄
  {ℓᵣ₁ ℓᵣ₂ ℓᵣ₃} {Y : Type{ℓᵣ₁}} ⦃ equiv : Equiv(Y) ⦄ (𝓣ᵣ : PredSet{ℓᵣ₂}(PredSet{ℓᵣ₁ ⊔ ℓᵣ₃}(Y)))
  ⦃ _ : TopologicalSpace{ℓᵣ₁}{ℓᵣ₂}{ℓᵣ₃} (𝓣ᵣ) ⦄
  where
  open TopologicalSpace ⦃ … ⦄

  open import Logic.Predicate

  record ContinuousAt (f : X → Y) ⦃ _ : Function(f) ⦄ (x : X) : Stmt{Lvl.𝐒(ℓₗ₁ ⊔ ℓₗ₃ ⊔ ℓᵣ₁ ⊔ ℓᵣ₃) ⊔ ℓₗ₂ ⊔ ℓᵣ₂} where
    constructor intro
    field
      map : ∃(Neighborhood(f(x))) → ∃(Neighborhood(x))
      proof : ∀{NB@([∃]-intro B) : ∃(Neighborhood(f(x)))}
            → let ([∃]-intro A) = map(NB)
              in  (A ⊆ unmap f(B))

  Continuous : (f : X → Y) ⦃ _ : Function(f) ⦄ → Stmt{Lvl.𝐒(ℓₗ₁ ⊔ ℓₗ₃ ⊔ ℓᵣ₁ ⊔ ℓᵣ₃) ⊔ ℓₗ₂ ⊔ ℓᵣ₂}
  Continuous(f) = ∀{x} → ContinuousAt f(x)

module _
  {ℓₗ₁ ℓₗ₂ ℓₗ₃} {X : Type{ℓₗ₁}} ⦃ equiv : Equiv(X) ⦄ (𝓣ₗ : PredSet{ℓₗ₂}(PredSet{ℓₗ₁ ⊔ ℓₗ₃}(X)))
  ⦃ _ : TopologicalSpace{ℓₗ₁}{ℓₗ₂}{ℓₗ₃} (𝓣ₗ) ⦄
  {ℓᵣ₁ ℓᵣ₂ ℓᵣ₃} {Y : Type{ℓᵣ₁}} ⦃ equiv : Equiv(Y) ⦄ (𝓣ᵣ : PredSet{ℓᵣ₂}(PredSet{ℓᵣ₁ ⊔ ℓᵣ₃}(Y)))
  ⦃ _ : TopologicalSpace{ℓᵣ₁}{ℓᵣ₂}{ℓᵣ₃} (𝓣ᵣ) ⦄
  where
  open TopologicalSpace ⦃ … ⦄

  open import Function.Inverse
  open import Structure.Function.Domain hiding (bijective)

  record Homeomorphism (f : X → Y) ⦃ _ : Function(f) ⦄ : Stmt{Lvl.𝐒(ℓₗ₁ ⊔ ℓₗ₃ ⊔ ℓᵣ₁ ⊔ ℓᵣ₃) ⊔ ℓₗ₂ ⊔ ℓᵣ₂} where
    constructor intro
    field
      ⦃ bijective ⦄          : Bijective(f)
      ⦃ continuous ⦄         : Continuous(𝓣ₗ)(𝓣ᵣ) (f)
      ⦃ continuous-inverse ⦄ : Continuous(𝓣ᵣ)(𝓣ₗ) (inv f) ⦃ inv-function ⦄
