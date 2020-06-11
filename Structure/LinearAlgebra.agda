-- Finite-dimensional linear algebra
module Structure.LinearAlgebra where

import      Lvl
open import Data
open import Data.Boolean.Stmt
open import Data.Tuple as Tuple using (_,_)
open import Functional using (id ; _∘_ ; _∘₂_ ; _$_ ; swap ; _on₂_)
open import Function.Equals
open import Function.Proofs
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.CoordinateVector as Vec using () renaming (Vector to Vec)
open import Numeral.Finite
open import Numeral.Natural
open import Numeral.Natural.Oper.Comparisons
open import Sets.ExtensionalPredicateSet as PredSet using (PredSet ; _∈_ ; [∋]-binaryRelator)
open import Structure.Setoid.WithLvl
open import Structure.Function.Domain
import      Structure.Function.Linear as Linear
open import Structure.Operator.Field
open import Structure.Operator.Group
open import Structure.Operator.Properties
open import Structure.Operator.Vector
open import Syntax.Function
open import Syntax.Number
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₗ ℓᵥ ℓₛ ℓᵥₑ ℓₛₑ : Lvl.Level
private variable V S : Type{ℓ}
private variable n n₁ n₂ : ℕ

module _
  {V : Type{ℓᵥ}} ⦃ equiv-V : Equiv{ℓᵥₑ}(V) ⦄
  {S : Type{ℓₛ}} ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄
  (_+ᵥ_ : V → V → V)
  (_⋅ₛᵥ_ : S → V → V)
  (_+ₛ_ _⋅ₛ_ : S → S → S)
  ⦃ vectorSpace : VectorSpace(_+ᵥ_)(_⋅ₛᵥ_)(_+ₛ_)(_⋅ₛ_) ⦄
  where
  open VectorSpace(vectorSpace)

  -- A linear combination constructed from a sequence of vectors and a sequence of scalars.
  -- Linear combination of 0 scalars and vectors are the zero vector.
  -- Linear combination of 1 scalar and vector is just scalar on vector multiplication.
  -- Example: LinearCombination {4} sf vf = (sf[0] ⋅ₛᵥ vf[0]) +ᵥ (sf[1] ⋅ₛᵥ vf[1]) +ᵥ (sf[2] ⋅ₛᵥ vf[2]) +ᵥ (sf[3] ⋅ₛᵥ vf[3])
  -- Inlined definition:
  --   LinearCombination {0}       _  _  = 𝟎ᵥ
  --   LinearCombination {1}       vf sf = Vec.proj(sf)(0) ⋅ₛᵥ Vec.proj(vf)(0)
  --   LinearCombination {𝐒(𝐒(n))} vf sf = (Vec.proj(sf)(0) ⋅ₛᵥ Vec.proj(vf)(0)) +ᵥ (LinearCombination {𝐒(n)} (Vec.tail vf) (Vec.tail sf))
  linearCombination : Vec(n)(V) → Vec(n)(S) → V
  linearCombination = Vec.reduceOrᵣ(_+ᵥ_) 𝟎ᵥ ∘₂ Vec.map₂(_⋅ᵥₛ_)

  -- This states that all finite sequences `vf` of length `n` (in terms of `Vec`) that consists of elements from the set `vs` satisfies `P`.
  -- This can be used in infinite-dimensional vector spaces to define linear independence, span and basis by: `∃(n ↦ AllFiniteSubsets(n)(P)(vs))`
  AllFiniteSubsets : (n : ℕ) → (Vec(n)(V) → Stmt{ℓ}) → (PredSet{ℓₗ}(V) → Stmt)
  AllFiniteSubsets(n) P(vs) = (∀{vf : Vec(n)(V)} ⦃ distinct : Vec.Distinct(vf) ⦄ → (∀{i : 𝕟(n)} → (Vec.proj(vf)(i) ∈ vs)) → P(vf))

  -- Whether the two specified vectors are linearly dependent or not.
  -- TODO: Is this definition neccessary?
  LinearlyDependentPair : V → V → Stmt
  LinearlyDependentPair v₁ v₂ = ∃(s₁ ↦ ∃(s₂ ↦ s₁ ⋅ₛᵥ v₁ ≡ s₂ ⋅ₛᵥ v₂))

  -- A sequence of vectors is linearly independent when there is no vector that can be represented as a linear combination by the others.
  -- Note: Equivalent to: `∀{sf} → (linearCombination(vf)(sf) ≡ 𝟎ᵥ) → (sf ⊜ Vec.fill(𝟎ₛ))`.
  LinearlyIndependent : Vec(n)(V) → Stmt
  LinearlyIndependent = Injective ∘ linearCombination

  -- A sequence of vectors is spanning the vector space when every vector in the vector space can be represented as a linear combination of the set of vectors.
  Spanning : Vec(n)(V) → Stmt
  Spanning = Surjective ∘ linearCombination

  -- A sequence of vectors is a basis when every vector in the vector space can be represented as a unique linear combination of the set of vectors.
  -- A sequence of vectors is a basis when they span the vector space and is linearly independent.
  Basis : Vec(n)(V) → Stmt
  Basis = Bijective ∘ linearCombination

  -- v is a eigenvector for the eigenvalue 𝜆 of the linear transformation f.
  -- Multiplication by an eigenvalue can replace a linear transformation for certain vectors.
  Eigenpair : (V → V) → S → V → Stmt
  Eigenpair(f)(𝜆)(v) = ((v ≢ 𝟎ᵥ) ∧ (f(v) ≡ 𝜆 ⋅ₛᵥ v))

  Eigenvector : (V → V) → V → Stmt
  Eigenvector(f)(v) = ∃(𝜆 ↦ Eigenpair(f)(𝜆)(v))

  Eigenvalue : (V → V) → S → Stmt
  Eigenvalue(f)(𝜆) = ∃(v ↦ Eigenpair(f)(𝜆)(v))

  module _ where
    open import Logic.Predicate.Equiv
    open import Structure.Container.SetLike using (SetElement)
    private open module SetLikeFunctionProperties{ℓ} = Structure.Container.SetLike.FunctionProperties{C = PredSet{ℓ}(V)}{E = V}(_∈_)
    open import Structure.Operator
    open import Structure.Operator.Proofs.Util
    open import Structure.Relator
    open import Structure.Relator.Properties
    open import Syntax.Transitivity

    -- A subspace is a subset of V such that it is a vector space under the same operators.
    record Subspace (Vₛ : PredSet{ℓ}(V)) : Stmt{ℓᵥ Lvl.⊔ ℓₛ Lvl.⊔ ℓ} where
      constructor intro
      field
        ⦃ add-closure ⦄ : Vₛ closed-under₂ (_+ᵥ_)
        ⦃ mul-closure ⦄ : ∀{s} → (Vₛ closed-under₁ (s ⋅ₛᵥ_))

      _+_ : SetElement(_∈_)(Vₛ) → SetElement(_∈_)(Vₛ) → SetElement(_∈_)(Vₛ)
      ([∃]-intro v₁ ⦃ p₁ ⦄) + ([∃]-intro v₂ ⦃ p₂ ⦄) = [∃]-intro(v₁ +ᵥ v₂) ⦃ (Vₛ closureUnder₂ (_+ᵥ_)) p₁ p₂ ⦄

      _⋅_ : S → SetElement(_∈_)(Vₛ) → SetElement(_∈_)(Vₛ)
      s ⋅ ([∃]-intro v ⦃ p ⦄) = [∃]-intro (s ⋅ₛᵥ v) ⦃ (Vₛ closureUnder₁ (s ⋅ₛᵥ_)) p ⦄

      -- TODO: A proof of this would be easier if a similar "substructure" relation was defined on groups and fields, but I am not sure if using PredSet is the correct choice (maybe this is unprovable when using this?). Another alternative is to use a general set structure by Structure.Container.SetLike
      postulate is-vectorSpace : VectorSpace{V = SetElement(_∈_)(Vₛ)}{S = S}(_+_)(_⋅_)(_+ₛ_)(_⋅ₛ_)
      -- is-vectorSpace = {!!}

    SubspaceObject : ∀{ℓ} → Stmt
    SubspaceObject{ℓ} = ∃(Subspace{ℓ})

    Span : Vec(n)(V) → PredSet(V)
    Span(vf) = PredSet.⊶(linearCombination(vf))

    -- TODO: This operator can also be constructed for vector spaces, not just subspaces
    _⊕ˢᵘᵇ_ : SubspaceObject{ℓ₁} → SubspaceObject{ℓ₂} → SubspaceObject
    ([∃]-intro V₁ ⦃ p₁ ⦄) ⊕ˢᵘᵇ ([∃]-intro V₂ ⦃ p₂ ⦄) = [∃]-intro (PredSet.map₂(_+ᵥ_) V₁ V₂) ⦃ p ⦄ where
      p : Subspace(PredSet.map₂(_+ᵥ_) V₁ V₂)
      ∃.witness (Structure.Container.SetLike.FunctionProperties._closed-under₂_.proof (Subspace.add-closure p) ([∃]-intro(a₁ , a₂)) ([∃]-intro(b₁ , b₂))) = ((a₁ +ᵥ b₁) , (a₂ +ᵥ b₂))
      ∃.proof (Structure.Container.SetLike.FunctionProperties._closed-under₂_.proof (Subspace.add-closure p) {a}{b} ([∃]-intro ([∧]-intro a₁ a₂) ⦃ [∧]-intro ([∧]-intro a₁V₁ a₂V₂) a₁a₂a ⦄) ([∃]-intro (b₁ , b₂) ⦃ [∧]-intro ([∧]-intro b₁V₁ b₂V₂) b₁b₂b ⦄)) = [∧]-intro ([∧]-intro l₁ l₂) r where
        l₁ : (a₁ +ᵥ b₁) ∈ V₁
        l₁ = (V₁ closureUnder₂(_+ᵥ_)) a₁V₁ b₁V₁
        l₂ : (a₂ +ᵥ b₂) ∈ V₂
        l₂ = (V₂ closureUnder₂(_+ᵥ_)) a₂V₂ b₂V₂
        r : (a₁ +ᵥ b₁) +ᵥ (a₂ +ᵥ b₂) ≡ a +ᵥ b
        r =
          (a₁ +ᵥ b₁) +ᵥ (a₂ +ᵥ b₂) 🝖[ _≡_ ]-[ One.associate-commute4-c {_▫_ = _+ᵥ_} ⦃ op = [+ᵥ]-binary-operator ⦄ ⦃ assoc = [+ᵥ]-associativity ⦄ ⦃ comm = [+ᵥ]-commutativity ⦄ ] -- TODO: Why are the instances not inferred?
          (a₁ +ᵥ a₂) +ᵥ (b₁ +ᵥ b₂) 🝖[ _≡_ ]-[ congruence₂(_+ᵥ_) ⦃ [+ᵥ]-binary-operator ⦄ a₁a₂a b₁b₂b ]
          a +ᵥ b                   🝖-end
      ∃.witness (Structure.Container.SetLike.FunctionProperties._closed-under₁_.proof (Subspace.mul-closure p {s}) ([∃]-intro(v₁ , v₂))) = ((s ⋅ₛᵥ v₁) , (s ⋅ₛᵥ v₂))
      ∃.proof (Structure.Container.SetLike.FunctionProperties._closed-under₁_.proof (Subspace.mul-closure p {s}) {v} ([∃]-intro(v₁ , v₂) ⦃ [∧]-intro ([∧]-intro v₁V₁ v₂V₂) v₁v₂v ⦄)) = [∧]-intro ([∧]-intro l₁ l₂) r where
        l₁ : (s ⋅ₛᵥ v₁) ∈ V₁
        l₁ = (V₁ closureUnder₁(s ⋅ₛᵥ_)) v₁V₁
        l₂ : (s ⋅ₛᵥ v₂) ∈ V₂
        l₂ = (V₂ closureUnder₁(s ⋅ₛᵥ_)) v₂V₂
        r : (s ⋅ₛᵥ v₁) +ᵥ (s ⋅ₛᵥ v₂) ≡ (s ⋅ₛᵥ v)
        r =
          (s ⋅ₛᵥ v₁) +ᵥ (s ⋅ₛᵥ v₂) 🝖[ _≡_ ]-[ distributivityₗ(_⋅ₛᵥ_)(_+ᵥ_) ]-sym
          s ⋅ₛᵥ (v₁ +ᵥ v₂)         🝖[ _≡_ ]-[ congruence₂ᵣ(_⋅ₛᵥ_)(s) v₁v₂v ]
          s ⋅ₛᵥ v                  🝖-end

  -- TODO: Formulate
  -- [⊕ˢᵘᵇ]-span-vectorSpace : (V₁ ⊕ V₂ ⊕ … ≡ₛ 𝐔) ↔ (∀{v₁}{v₂}{…} → (v₁ ∈ V₁) → (v₂ ∈ V₂) → … → (v₁ + v₂ + … ≡ 𝟎ᵥ) → ((v₁ ≡ 𝟎ᵥ) ∧ (v₂ ≡ 𝟎ᵥ) ∧ …))
  -- [⊕ˢᵘᵇ]-span-existence-finite-space : Finite → ∃(\{(V₁ , V₂ , …) → V₁ ⊕ V₂ ⊕ … ≡ₛ 𝐔}) -- TODO: Just take the "standard" "axis aligned" subspaces

  open import Logic.Classical
  open import Numeral.CoordinateVector.Proofs
  open import Numeral.Natural.Relation.Order
  open import Numeral.Natural.Relation.Order.Proofs
  import      Relator.Equals as Eq
  open import Relator.Equals.Proofs.Equivalence
  open import Structure.Function.Domain.Proofs
  open import Structure.Function.Multi
  import      Structure.Function.Names as Names
  open import Structure.Operator.Proofs
  open import Structure.Operator.Proofs.Util
  open import Structure.Operator
  open import Structure.Operator.Vector.Proofs
  open import Structure.Relator.Properties
  open import Syntax.Transitivity

  private variable vf vf₁ vf₂ : Vec(n)(V)
  private variable sf sf₁ sf₂ : Vec(n)(S)
  private variable i j : 𝕟(n)

  instance
    linearCombination-binaryOperator : BinaryOperator(linearCombination{n})
    linearCombination-binaryOperator = intro p where
      p : Names.Congruence₂(linearCombination{n})
      p {𝟎}       {vf₁} {vf₂} (intro vfeq) {sf₁} {sf₂} (intro sfeq) = reflexivity(_≡_)
      p {𝐒(𝟎)}    {vf₁} {vf₂} (intro vfeq) {sf₁} {sf₂} (intro sfeq) = congruence₂(_⋅ₛᵥ_) sfeq vfeq
      p {𝐒(𝐒(n))} {vf₁} {vf₂} (intro vfeq) {sf₁} {sf₂} (intro sfeq) =
        (sf₁(𝟎) ⋅ₛᵥ vf₁(𝟎)) +ᵥ linearCombination(Vec.tail vf₁) (Vec.tail sf₁) 🝖[ _≡_ ]-[ congruence₂(_+ᵥ_) (congruence₂(_⋅ₛᵥ_) sfeq vfeq) (p {𝐒(n)} (intro vfeq) (intro sfeq)) ]
        (sf₂(𝟎) ⋅ₛᵥ vf₂(𝟎)) +ᵥ linearCombination(Vec.tail vf₂) (Vec.tail sf₂) 🝖-end

  instance
    linearCombination-scalar-preserves-[+] : Preserving₂(linearCombination vf) (Vec.map₂(_+ₛ_)) (_+ᵥ_)
    linearCombination-scalar-preserves-[+] {vf = vf} = intro(p{vf = vf}) where
      p : ∀{n}{vf : Vec(n)(V)} → Names.Preserving₂(linearCombination vf) (Vec.map₂(_+ₛ_)) (_+ᵥ_)
      p {𝟎}{vf} {sf₁} {sf₂} =
        𝟎ᵥ       🝖[ _≡_ ]-[ identityₗ(_+ᵥ_)(𝟎ᵥ) ]-sym
        𝟎ᵥ +ᵥ 𝟎ᵥ 🝖-end
      p {𝐒(𝟎)}{vf} {sf₁} {sf₂} =
        (Vec.map₂(_+ₛ_) sf₁ sf₂ 𝟎) ⋅ₛᵥ vf(𝟎)     🝖[ _≡_ ]-[]
        (sf₁(𝟎) +ₛ sf₂(𝟎)) ⋅ₛᵥ vf(𝟎)             🝖[ _≡_ ]-[ [⋅ₛᵥ][+ₛ][+ᵥ]-distributivityᵣ ]
        (sf₁(𝟎) ⋅ₛᵥ vf(𝟎)) +ᵥ (sf₂(𝟎) ⋅ₛᵥ vf(𝟎)) 🝖-end
      p {𝐒(𝐒(n))}{vf} {sf₁} {sf₂} =
        ((Vec.map₂(_+ₛ_) sf₁ sf₂ 𝟎) ⋅ₛᵥ vf(𝟎)) +ᵥ (linearCombination {𝐒(n)} (Vec.tail vf) (Vec.tail(Vec.map₂(_+ₛ_) sf₁ sf₂)))                                                🝖[ _≡_ ]-[]
        ((sf₁(𝟎) +ₛ sf₂(𝟎)) ⋅ₛᵥ vf(𝟎)) +ᵥ (linearCombination {𝐒(n)} (Vec.tail vf) (Vec.tail(Vec.map₂(_+ₛ_) sf₁ sf₂)))                                                        🝖[ _≡_ ]-[ congruence₂(_+ᵥ_) [⋅ₛᵥ][+ₛ][+ᵥ]-distributivityᵣ (p {𝐒(n)}{Vec.tail vf} {Vec.tail sf₁} {Vec.tail sf₂}) ]
        ((sf₁(𝟎) ⋅ₛᵥ vf(𝟎)) +ᵥ (sf₂(𝟎) ⋅ₛᵥ vf(𝟎))) +ᵥ ((linearCombination {𝐒(n)} (Vec.tail vf) (Vec.tail sf₁)) +ᵥ (linearCombination {𝐒(n)} (Vec.tail vf) (Vec.tail sf₂)))   🝖[ _≡_ ]-[ One.associate-commute4 (commutativity(_+ᵥ_)) ]
        (((sf₁(𝟎) ⋅ₛᵥ vf(𝟎)) +ᵥ (linearCombination {𝐒(n)} (Vec.tail vf) (Vec.tail sf₁))) +ᵥ ((sf₂(𝟎) ⋅ₛᵥ vf(𝟎)) +ᵥ (linearCombination {𝐒(n)} (Vec.tail vf) (Vec.tail sf₂)))) 🝖-end

  instance
    linearCombination-scalar-preserves-[⋅] : ∀{s} → Preserving₁(linearCombination vf) (Vec.map(s ⋅ₛ_)) (s ⋅ₛᵥ_)
    linearCombination-scalar-preserves-[⋅] {vf = vf} {s = s} = intro(p{vf = vf}) where
      p : ∀{n}{vf : Vec(n)(V)} → Names.Preserving₁(linearCombination vf) (Vec.map(s ⋅ₛ_)) (s ⋅ₛᵥ_)
      p {𝟎} {vf} {sf} =
        𝟎ᵥ       🝖[ _≡_ ]-[ [⋅ₛᵥ]-absorberᵣ ]-sym
        s ⋅ₛᵥ 𝟎ᵥ 🝖-end
      p {𝐒(𝟎)} {vf} {sf} =
        (s ⋅ₛ sf(𝟎)) ⋅ₛᵥ vf(𝟎)  🝖[ _≡_ ]-[ [⋅ₛ][⋅ₛᵥ]-compatibility ]
        s ⋅ₛᵥ (sf(𝟎) ⋅ₛᵥ vf(𝟎)) 🝖-end
      p {𝐒(𝐒(n))} {vf} {sf} =
        linearCombination vf (Vec.map (s ⋅ₛ_) sf)                                                     🝖[ _≡_ ]-[]
        ((s ⋅ₛ sf(𝟎)) ⋅ₛᵥ vf(𝟎)) +ᵥ (linearCombination (Vec.tail vf) (Vec.map (s ⋅ₛ_) (Vec.tail sf))) 🝖[ _≡_ ]-[ congruence₂(_+ᵥ_) ⦃ [+ᵥ]-binary-operator ⦄ [⋅ₛ][⋅ₛᵥ]-compatibility (p {𝐒(n)} {Vec.tail vf} {Vec.tail sf}) ]
        (s ⋅ₛᵥ (sf(𝟎) ⋅ₛᵥ vf(𝟎))) +ᵥ (s ⋅ₛᵥ (linearCombination (Vec.tail vf) (Vec.tail sf)))          🝖[ _≡_ ]-[ distributivityₗ(_⋅ₛᵥ_)(_+ᵥ_) ]-sym
        s ⋅ₛᵥ ((sf(𝟎) ⋅ₛᵥ vf(𝟎)) +ᵥ (linearCombination (Vec.tail vf) (Vec.tail sf)))                  🝖[ _≡_ ]-[]
        s ⋅ₛᵥ (linearCombination vf sf)                                                               🝖-end

  module _ where
    open import Logic.Predicate.Equiv
    open import Structure.Container.SetLike using (SetElement)
    private open module SetLikeFunctionProperties{ℓ} = Structure.Container.SetLike.FunctionProperties{C = PredSet{ℓ}(V)}{E = V}(_∈_)
    open import Structure.Function
    open import Structure.Operator
    open import Structure.Operator.Proofs.Util
    open import Structure.Relator
    open import Structure.Relator.Properties
    open import Syntax.Transitivity

    Span-subspace : ∀{vf} → Subspace(Span{n}(vf))
    ∃.witness (_closed-under₂_.proof (Subspace.add-closure (Span-subspace {vf = vf})) ([∃]-intro sf₁) ([∃]-intro sf₂)) = Vec.map₂(_+ₛ_) sf₁ sf₂
    ∃.proof (_closed-under₂_.proof (Subspace.add-closure (Span-subspace {vf = vf})) {v₁} {v₂} ([∃]-intro sf₁ ⦃ p₁ ⦄) ([∃]-intro sf₂ ⦃ p₂ ⦄)) =
      linearCombination vf (Vec.map₂(_+ₛ_) sf₁ sf₂)            🝖[ _≡_ ]-[ preserving₂(linearCombination vf) (Vec.map₂(_+ₛ_)) (_+ᵥ_) ]
      (linearCombination vf sf₁) +ᵥ (linearCombination vf sf₂) 🝖[ _≡_ ]-[ congruence₂(_+ᵥ_) ⦃ [+ᵥ]-binary-operator ⦄ p₁ p₂ ]
      v₁ +ᵥ v₂                                                 🝖-end
    ∃.witness (_closed-under₁_.proof (Subspace.mul-closure Span-subspace {s}) ([∃]-intro sf)) = Vec.map(s ⋅ₛ_) sf
    ∃.proof (_closed-under₁_.proof (Subspace.mul-closure (Span-subspace {vf = vf}) {s}) {v} ([∃]-intro sf ⦃ p ⦄)) =
      linearCombination vf (i ↦ s ⋅ₛ sf(i)) 🝖[ _≡_ ]-[ preserving₁(linearCombination vf) (Vec.map(s ⋅ₛ_)) (s ⋅ₛᵥ_) ]
      s ⋅ₛᵥ (linearCombination vf sf)       🝖[ _≡_ ]-[ congruence₂ᵣ(_⋅ₛᵥ_)(s) p ]
      s ⋅ₛᵥ v                               🝖-end

  -- A basis could essentially be defined as being linearly independent and spanning the vector space.
  linearIndependence-spanning-basis-equivalence : (LinearlyIndependent(vf) ∧ Spanning(vf)) ↔ Basis(vf)
  linearIndependence-spanning-basis-equivalence = injective-surjective-bijective-equivalence _

  -- Linearly independent sequence of vectors are vectors such that a linear combination of them never maps to zero.
  -- Note that this is the usual definition of linear independence.
  linearIndependence-equivalence : LinearlyIndependent(vf) ↔ (∀{sf} → (linearCombination(vf)(sf) ≡ 𝟎ᵥ) → (sf ⊜ Vec.fill(𝟎ₛ)))
  linearIndependence-equivalence =
    Two.injective-kernel
      {_▫₁_ = Vec.map₂(_+ₛ_)}
      ⦃ func = BinaryOperator.right linearCombination-binaryOperator ⦄
      ⦃ cancₗ₂ = One.cancellationₗ-by-associativity-inverse ⦄
      {inv₁ = Vec.map(−ₛ_)}

  -- linearCombination-of-unit : linearCombination vf (Vec.fill 𝟏ₛ) ≡ (foldᵣ(_+_) 𝟎ᵥ vf)
  postulate linearCombination-of-indexProject : (linearCombination vf (Vec.indexProject i 𝟏ₛ 𝟎ₛ) ≡ vf(i))

  postulate indexProject-true  : ∀{true false : S} → (i Eq.≡ j) ↔ (Vec.proj(Vec.indexProject i true false) i ≡ true)
  postulate indexProject-false : ∀{true false : S} → (i Eq.≢ j) ↔ (Vec.proj(Vec.indexProject i true false) j ≡ false)

  -- postulate linearCombination-when-zero : (linearCombination(vf)(sf) ≡ 𝟎ᵥ) → (∀{i} → (vf(i) ≡ 𝟎ᵥ) ∨ (sf(i) ≡ 𝟎ₛ))
  postulate [≡][𝕟]-classical : Classical(i Eq.≡ j)

  -- A sequence of vectors with a zero vector in it are not linearly independent, and a linearly independent sequence of vectors do not contain zero vectors.
  linearIndependence-no-zero-vectors : LinearlyIndependent(vf) → ∀{i} → (vf(i) ≡ 𝟎ᵥ) → ⊥
  linearIndependence-no-zero-vectors {𝐒(n)}{vf} li {i} vfzero = distinct-identitiesₛ $
    𝟎ₛ                         🝖[ _≡_ ]-[]
    Vec.fill 𝟎ₛ i              🝖[ _≡_ ]-[ _⊜_.proof ([↔]-to-[→] linearIndependence-equivalence li p) ]-sym
    Vec.indexProject i 𝟏ₛ 𝟎ₛ i 🝖[ _≡_ ]-[ [↔]-to-[→] (indexProject-true{i = i}{false = 𝟎ₛ}) (reflexivity(Eq._≡_)) ]
    𝟏ₛ                         🝖-end
    where
      p =
        linearCombination vf (Vec.indexProject i 𝟏ₛ 𝟎ₛ) 🝖[ _≡_ ]-[ linearCombination-of-indexProject{vf = vf} ]
        vf(i)                                           🝖[ _≡_ ]-[ vfzero ]
        𝟎ᵥ                                              🝖-end

  --∀{i} → (vf(i) ≡ 𝟎ᵥ) → Spanning{𝐒(n)}(vf) → Spanning{n}(Vec.without i vf)

  -- There are no duplicates in a sequence of linearly independent vectors.
  linearIndependence-to-distinct : LinearlyIndependent(vf) → Vec.Distinct(vf)
  Injective.proof (linearIndependence-to-distinct {vf = vf} (intro inj)) {x} {y} vfxy = [¬¬]-elim ⦃ [≡][𝕟]-classical ⦄ $ nxy ↦
    let
      p : linearCombination vf (Vec.indexProject x 𝟏ₛ 𝟎ₛ) ≡ linearCombination vf (Vec.indexProject y 𝟏ₛ 𝟎ₛ)
      p =
        linearCombination vf (Vec.indexProject x 𝟏ₛ 𝟎ₛ) 🝖[ _≡_ ]-[ linearCombination-of-indexProject{vf = vf} ]
        vf(x)                                           🝖[ _≡_ ]-[ vfxy ]
        vf(y)                                           🝖[ _≡_ ]-[ linearCombination-of-indexProject{vf = vf} ]-sym
        linearCombination vf (Vec.indexProject y 𝟏ₛ 𝟎ₛ) 🝖-end

      q : 𝟎ₛ ≡ 𝟏ₛ
      q =
        𝟎ₛ                                      🝖[ _≡_ ]-[ [↔]-to-[→] (indexProject-false{true = 𝟏ₛ}) nxy ]-sym
        Vec.proj(Vec.indexProject(x) 𝟏ₛ 𝟎ₛ) (y) 🝖[ _≡_ ]-[ _⊜_.proof(inj p) {y} ]
        Vec.proj(Vec.indexProject(y) 𝟏ₛ 𝟎ₛ) (y) 🝖[ _≡_ ]-[ [↔]-to-[→] (indexProject-true{false = 𝟎ₛ}) (reflexivity(Eq._≡_) {x = y}) ]
        𝟏ₛ                                      🝖-end
    in distinct-identitiesₛ q

  -- A subsequence of a linearly independent sequence of vectors are linearly independent.
  postulate independent-subsequence-is-independent : ∀{N : 𝕟(n₁) → 𝕟(n₂)} ⦃ inj : Injective ⦃ [≡]-equiv ⦄ ⦃ [≡]-equiv ⦄ (N) ⦄ → LinearlyIndependent{n₂}(vf) → LinearlyIndependent{n₁}(vf ∘ N)

  postulate linear-independent-sequence-set-equivalence : ∀{N : 𝕟(n₁) → 𝕟(n₂)} ⦃ bij : Bijective ⦃ [≡]-equiv ⦄ ⦃ [≡]-equiv ⦄ (N)⦄ → LinearlyIndependent{n₂}(vf) ↔ LinearlyIndependent{n₁}(vf ∘ N)

  postulate spanning-supersequence-is-spanning : ∀{N : 𝕟(n₁) → 𝕟(n₂)} ⦃ surj : Surjective ⦃ [≡]-equiv ⦄ (N) ⦄ → Spanning{n₂}(vf) → Spanning{n₁}(vf ∘ N)

  postulate spanning-sequence-set-equivalence : ∀{N : 𝕟(n₁) → 𝕟(n₂)} ⦃ bij : Bijective ⦃ [≡]-equiv ⦄ ⦃ [≡]-equiv ⦄ (N) ⦄ → Spanning{n₂}(vf) ↔ Spanning{n₁}(vf ∘ N)

  -- The number of linearly independent vectors is always less than the cardinality of a set of spanning vectors.
  -- TODO: It is important to prove this if possible
  postulate independent-less-than-spanning : ∀{n₁}{vf₁} → LinearlyIndependent{n₁}(vf₁) → ∀{n₂}{vf₂} → Spanning{n₂}(vf₂) → (n₁ ≤ n₂)
  {- TODO: Here is an idea of a proof, but it probably requires more development in the theory of cardinalities
    LinearlyIndependent{n₁}(vf₁)
    Injective(linearCombination{n = n₁}(vf₁)) (essentially: Vec(n₁)(S) ≤ V)

    Spanning{n₂}(vf₂)
    Surjective(linearCombination{n = n₂}(vf₂)) (essentially: Vec(n₂)(S) ≥ V)
    Injective(linearCombination{n = n₂}(vf₂) ∘ inv) (Is this really true then? Essentially: V ≤ Vec(n₂)(S))

    Injective(linearCombination{n = n₂}(vf₂) ∘ inv ∘ linearCombination{n = n₁}(vf₁)) (essentially: Vec(n₁)(S) ≤ Vec(n₂)(S))
    n₁ ≤ n₂ (Note: This is not true in general. Only if the morphism is the "natural one" (the 𝟎 ↦ 𝟎 and n-tuples only maps to n-tuples and so on)), but is it really obtained by the proofs above?
  -}

  -- Two bases in a vector space are always of the same length.
  basis-equal-length : Basis{n₁}(vf₁) → Basis{n₂}(vf₂) → (n₁ Eq.≡ n₂)
  basis-equal-length b₁ b₂
    with (li₁ , sp₁) ← [↔]-to-[←] linearIndependence-spanning-basis-equivalence b₁
    |    (li₂ , sp₂) ← [↔]-to-[←] linearIndependence-spanning-basis-equivalence b₂
    = antisymmetry(_≤_)(Eq._≡_) (independent-less-than-spanning li₁ sp₂) (independent-less-than-spanning li₂ sp₁)

  -- A finite basis can always be constructed by a subsequence of a finite spanning sequence of vectors.
  -- TODO: One way of proving this is by assuming that the relation LinearlyIndependent is decidable (it is because of the isomorphism from matrices (all vector spaces of the same dimension are isomorphic) and then matrix operations can tell whether a set of finite vectors are decidable), and then remove vectors one by one from the spanning sequence until it is linearly independent (which it will be at the end. In extreme cases, a sequence of zero vectors are linearly independent). This algorithm will always terminate because all vectors are finite, but how will this be shown?
  postulate basis-subsequence-from-spanning : Spanning{n₂}(vf) → ∃(n₁ ↦ ∃{Obj = 𝕟(n₁) → 𝕟(n₂)}(N ↦ Injective ⦃ [≡]-equiv ⦄ ⦃ [≡]-equiv ⦄ (N) ∧ Basis{n₁}(vf ∘ N)))

  -- A finite dimensional vector space is when there are a finite number of vectors that spans the whole space.
  FiniteDimensional : Stmt
  FiniteDimensional = ∃(n ↦ ∃(vf ↦ Spanning{n}(vf)))

  module _ ⦃ fin-dim@([∃]-intro(spanSize) ⦃ [∃]-intro span ⦃ span-spanning ⦄ ⦄) : FiniteDimensional ⦄ where
    -- A basis always exists for finite vector spaces.
    basis-existence : ∃(n ↦ ∃(vf ↦ Basis{n}(vf)))
    basis-existence
      with [∃]-intro(n) ⦃ [∃]-intro N ⦃ [∧]-intro inj basis ⦄ ⦄ ← basis-subsequence-from-spanning span-spanning
      = [∃]-intro(n) ⦃ [∃]-intro (span ∘ N) ⦃ basis ⦄ ⦄

    -- The dimension of the vector space is the length of a basis, which are the same for every vector space.
    dim : ℕ
    dim = [∃]-witness basis-existence

    postulate basis-supersequence-from-linear-independence : LinearlyIndependent{n₂}(vf) → ∃(n₁ ↦ ∃{Obj = 𝕟(n₁) → 𝕟(n₂)}(N ↦ Surjective ⦃ [≡]-equiv ⦄ (N) ∧ Basis{n₁}(vf ∘ N)))
    -- TODO: One idea is to start with vf. Then try to add the basis vectors one by one from basis-existence while maintaining the linear independence

    postulate independence-spanning-equivalence-for-dimension : LinearlyIndependent{dim}(vf) ↔ Spanning{dim}(vf)

  InfiniteDimensional = ∀{n} → ∃(vf ↦ LinearlyIndependent{n}(vf))

-- TODO: For this to be formulated, reorganize some stuff
-- finite-subspace-set-equality : ∀{Vₛ₁ Vₛ₂} → Subspace(Vₛ₁) → Subspace(Vₛ₂) → (dim(Vₛ₁) ≡ dim(Vₛ₂)) → (Vₛ₁ ≡ Vₛ₂) -- as in set equality
