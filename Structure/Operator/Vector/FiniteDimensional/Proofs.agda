import      Lvl
open import Structure.Operator.Vector
open import Structure.Setoid.WithLvl
open import Type

module Structure.Operator.Vector.FiniteDimensional.Proofs
  {ℓᵥ ℓₛ ℓᵥₑ ℓₛₑ}
  {V : Type{ℓᵥ}} ⦃ equiv-V : Equiv{ℓᵥₑ}(V) ⦄
  {S : Type{ℓₛ}} ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄
  {_+ᵥ_ : V → V → V}
  {_⋅ₛᵥ_ : S → V → V}
  {_+ₛ_ _⋅ₛ_ : S → S → S}
  ⦃ vectorSpace : VectorSpace(_+ᵥ_)(_⋅ₛᵥ_)(_+ₛ_)(_⋅ₛ_) ⦄
  where

open VectorSpace(vectorSpace)

open import Data.Tuple as Tuple using (_,_)
open import Functional using (id ; _∘_ ; _∘₂_ ; _$_ ; swap ; _on₂_)
open import Function.Equals
open import Logic
open import Logic.Classical
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.CoordinateVector as Vec using () renaming (Vector to Vec)
open import Numeral.CoordinateVector.Proofs
open import Numeral.Finite
open import Numeral.Finite.Proofs
open import Numeral.Natural
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
import      Relator.Equals as Eq
open import Relator.Equals.Proofs.Equivalence
open import Structure.Function.Domain
open import Structure.Function.Domain.Proofs
open import Structure.Operator.Proofs
open import Structure.Operator
open import Structure.Operator.Vector.FiniteDimensional        ⦃ vectorSpace = vectorSpace ⦄
open import Structure.Operator.Vector.LinearCombination        ⦃ vectorSpace = vectorSpace ⦄
open import Structure.Operator.Vector.LinearCombination.Proofs
open import Structure.Relator.Properties
open import Syntax.Function
open import Syntax.Number
open import Syntax.Transitivity

private variable ℓ ℓ₁ ℓ₂ ℓₗ : Lvl.Level
private variable n n₁ n₂ : ℕ

private variable vf vf₁ vf₂ : Vec(n)(V)
private variable sf sf₁ sf₂ : Vec(n)(S)
private variable i j : 𝕟(n)

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

-- postulate linearCombination-when-zero : (linearCombination(vf)(sf) ≡ 𝟎ᵥ) → (∀{i} → (vf(i) ≡ 𝟎ᵥ) ∨ (sf(i) ≡ 𝟎ₛ))

-- A sequence of vectors with a zero vector in it are not linearly independent, and a linearly independent sequence of vectors do not contain zero vectors.
linearIndependence-no-zero-vectors : LinearlyIndependent(vf) → ∀{i} → (vf(i) ≡ 𝟎ᵥ) → ⊥
linearIndependence-no-zero-vectors {𝐒(n)}{vf} li {i} vfzero = distinct-identitiesₛ $
  𝟎ₛ                         🝖[ _≡_ ]-[]
  Vec.fill 𝟎ₛ i              🝖[ _≡_ ]-[ _⊜_.proof ([↔]-to-[→] linearIndependence-equivalence li p) ]-sym
  Vec.indexProject i 𝟏ₛ 𝟎ₛ i 🝖[ _≡_ ]-[ [↔]-to-[→] (indexProject-true{i = i}{false = 𝟎ₛ}) ([∨]-introₗ(reflexivity(Eq._≡_))) ]
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
      𝟎ₛ                                      🝖[ _≡_ ]-[ [↔]-to-[→] (indexProject-false{true = 𝟏ₛ}) ([∨]-introₗ nxy) ]-sym
      Vec.proj(Vec.indexProject(x) 𝟏ₛ 𝟎ₛ) (y) 🝖[ _≡_ ]-[ _⊜_.proof(inj p) {y} ]
      Vec.proj(Vec.indexProject(y) 𝟏ₛ 𝟎ₛ) (y) 🝖[ _≡_ ]-[ [↔]-to-[→] (indexProject-true{false = 𝟎ₛ}) ([∨]-introₗ(reflexivity(Eq._≡_) {x = y})) ]
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
{- TODO: Here is an idea of a proof, but it probably requires more development in the theory of cardinalities. Or maybe just some stuff on linearCombination
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


module _ ⦃ fin-dim@([∃]-intro(spanSize) ⦃ [∃]-intro span ⦃ span-spanning ⦄ ⦄) : FiniteDimensional ⦄ where
  -- A basis always exists for finite dimensional vector spaces.
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


-- TODO: For this to be formulated, reorganize some stuff
-- finite-subspace-set-equality : ∀{Vₛ₁ Vₛ₂} → Subspace(Vₛ₁) → Subspace(Vₛ₂) → (dim(Vₛ₁) ≡ dim(Vₛ₂)) → (Vₛ₁ ≡ Vₛ₂) -- as in set equality
