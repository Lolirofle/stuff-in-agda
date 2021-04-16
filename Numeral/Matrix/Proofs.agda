module Numeral.Matrix.Proofs where

import      Lvl
open import Syntax.Number
open import Data
open import Data.Boolean
open import Data.Boolean.Stmt
open import Data.Boolean.Stmt.Proofs
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
import      Functional as Fn
open import Function.Equals
open import Lang.Inspect
open import Logic.Predicate
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Numeral.Finite
open import Numeral.Finite.Bound
open import Numeral.Finite.Oper
open import Numeral.Finite.Oper.Comparisons
open import Numeral.Finite.Oper.Comparisons.Proofs
open import Numeral.Finite.Proofs
open import Numeral.Matrix as Matrix using (Matrix ; SquareMatrix)
open import Numeral.Natural
open import Numeral.CoordinateVector as Vector using (Vector)
import      Numeral.CoordinateVector.Proofs as Vector
open import Relator.Equals using ([≡]-intro) renaming (_≡_ to _≡ₑ_ ; _≢_ to _≢ₑ_)
open import Relator.Equals.Proofs.Equivalence
open import Structure.Function
open import Structure.Operator.Group
open import Structure.Operator.Monoid
open import Structure.Operator.Properties
open import Structure.Operator
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Setoid
open import Syntax.Function
open import Syntax.Implication
open import Syntax.Transitivity
open import Type

private variable ℓ ℓₑ : Lvl.Level
private variable T A B : Type{ℓ}

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  private variable s : ℕ ⨯ ℕ
  private variable w h n : ℕ
  private variable x y z : 𝕟(n)
  private variable id id₁ id₂ zero elem 𝟎ₛ 𝟏ₛ : T
  private variable f g inv : T → T
  private variable _▫_ _▫₁_ _▫₂_ _+ₛ_ _⋅ₛ_ : T → T → T
  private variable v v₁ v₂ : Vector(n)(T)
  private variable M : Matrix(s)(T)

  instance
    matrix-equiv : Equiv(Matrix(s)(T))
    Equiv._≡_ matrix-equiv (Matrix.mat proj₁) (Matrix.mat proj₂) = proj₁ ⊜ proj₂
    Reflexivity.proof  (Equivalence.reflexivity  (Equiv.equivalence matrix-equiv)) = reflexivity(_⊜_)
    Symmetry.proof     (Equivalence.symmetry     (Equiv.equivalence matrix-equiv)) = symmetry(_⊜_)
    Transitivity.proof (Equivalence.transitivity (Equiv.equivalence matrix-equiv)) = transitivity(_⊜_)

  instance
    matrix-map₂-binaryOperator : ⦃ oper : BinaryOperator(_▫_) ⦄ → BinaryOperator(Matrix.map₂{s = s}(_▫_))
    BinaryOperator.congruence (matrix-map₂-binaryOperator {_▫_ = _▫_} ⦃ oper ⦄) (intro p) (intro q) = intro (congruence₂(_▫_) ⦃ oper ⦄ p q)

  instance
    matrix-map₂-identityₗ : ⦃ ident : Identityₗ(_▫_)(id) ⦄ → Identityₗ(Matrix.map₂{s = s}(_▫_)) (Matrix.fill(id))
    Identityₗ.proof (matrix-map₂-identityₗ {_▫_ = _▫_} {id = id}) = intro(identityₗ(_▫_)(id))

  instance
    matrix-map₂-identityᵣ : ⦃ ident : Identityᵣ(_▫_)(id) ⦄ → Identityᵣ(Matrix.map₂{s = s}(_▫_)) (Matrix.fill(id))
    Identityᵣ.proof (matrix-map₂-identityᵣ {_▫_ = _▫_} {id = id}) = intro(identityᵣ(_▫_)(id))

  instance
    matrix-map₂-identity : ⦃ ident : Identity(_▫_)(id) ⦄ → Identity(Matrix.map₂{s = s}(_▫_)) (Matrix.fill(id))
    matrix-map₂-identity = intro

  instance
    matrix-map₂-absorberₗ : ⦃ absorb : Absorberₗ(_▫_)(id) ⦄ → Absorberₗ(Matrix.map₂{s = s}(_▫_)) (Matrix.fill(id))
    Absorberₗ.proof (matrix-map₂-absorberₗ {_▫_ = _▫_} {id = id}) = intro(absorberₗ(_▫_)(id))

  instance
    matrix-map₂-absorberᵣ : ⦃ absorb : Absorberᵣ(_▫_)(id) ⦄ → Absorberᵣ(Matrix.map₂{s = s}(_▫_)) (Matrix.fill(id))
    Absorberᵣ.proof (matrix-map₂-absorberᵣ {_▫_ = _▫_} {id = id}) = intro(absorberᵣ(_▫_)(id))

  instance
    matrix-map₂-absorber : ⦃ absorb : Absorber(_▫_)(id) ⦄ → Absorber(Matrix.map₂{s = s}(_▫_)) (Matrix.fill(id))
    matrix-map₂-absorber = intro

  instance
    matrix-map₂-commutativity : ⦃ comm : Commutativity(_▫_) ⦄ → Commutativity(Matrix.map₂{s = s}(_▫_))
    Commutativity.proof (matrix-map₂-commutativity {_▫_ = _▫_}) = intro(commutativity(_▫_))

  instance
    matrix-map₂-associativity : ⦃ assoc : Associativity(_▫_) ⦄ → Associativity(Matrix.map₂{s = s}(_▫_))
    Associativity.proof (matrix-map₂-associativity {_▫_ = _▫_}) = intro(associativity(_▫_))

  instance
    matrix-map₂-map-inverseFunctionₗ : ⦃ ident : Identityₗ(_▫_)(id) ⦄ ⦃ inver : InverseFunctionₗ(_▫_) ⦃ [∃]-intro _ ⦄ (inv) ⦄ → InverseFunctionₗ(Matrix.map₂{s = s}(_▫_)) ⦃ [∃]-intro _ ⦄ (Matrix.map inv)
    InverseFunctionₗ.proof (matrix-map₂-map-inverseFunctionₗ {_▫_ = _▫_} {inv = inv}) = intro (inverseFunctionₗ(_▫_) ⦃ [∃]-intro _ ⦄ (inv))

  instance
    matrix-map₂-map-inverseFunctionᵣ : ⦃ ident : Identityᵣ(_▫_)(id) ⦄ ⦃ inver : InverseFunctionᵣ(_▫_) ⦃ [∃]-intro _ ⦄ (inv) ⦄ → InverseFunctionᵣ(Matrix.map₂{s = s}(_▫_)) ⦃ [∃]-intro _ ⦄ (Matrix.map inv)
    InverseFunctionᵣ.proof (matrix-map₂-map-inverseFunctionᵣ {_▫_ = _▫_} {inv = inv}) = intro (inverseFunctionᵣ(_▫_) ⦃ [∃]-intro _ ⦄ (inv))

  instance
    matrix-map₂-map-inverseFunction : ⦃ ident : Identity(_▫_)(id) ⦄ ⦃ inver : InverseFunction(_▫_) ⦃ [∃]-intro _ ⦄ (inv) ⦄ → InverseFunction(Matrix.map₂{s = s}(_▫_)) ⦃ [∃]-intro _ ⦄ (Matrix.map inv)
    matrix-map₂-map-inverseFunction = intro

  instance
    matrix-map-function : ⦃ func : Function(f) ⦄ → Function(Matrix.map{s = s} (f))
    Function.congruence matrix-map-function (intro p) = intro(congruence₁ _ p)

  instance
    matrix-map₂-monoid : ⦃ monoid : Monoid(_▫_) ⦄ → Monoid(Matrix.map₂{s = s}(_▫_))
    Monoid.identity-existence matrix-map₂-monoid = [∃]-intro(Matrix.fill(_))

  instance
    matrix-map₂-group : ⦃ group : Group(_▫_) ⦄ → Group(Matrix.map₂{s = s}(_▫_))
    Group.monoid matrix-map₂-group = matrix-map₂-monoid
    Group.inverse-existence matrix-map₂-group = [∃]-intro _

  diagMat-element-zero : (Matrix.proj (SquareMatrix.diagMat zero v) (x , y) ≡ zero) ↔ ((x ≢ₑ y) ∨ (Vector.proj v(x) ≡ zero))
  diagMat-element-zero {zero = zero}{𝐒 n}{v = v}{x = x}{y = y} =
    [↔]-intro ([↔]-to-[←] [→ₗ][∨][∧]-preserving ([∧]-intro l₁ l₂)) r ⦗ [↔]-transitivity ⦘ᵣ
    [∨]-mapₗ-[↔] ([↔]-transitivity false-true-opposites ([↔]-symmetry([¬]-unaryOperator [≡][≡?]-equivalence)))
    where
      l₁ : (Matrix.proj (SquareMatrix.diagMat zero v) (x , y) ≡ zero) ← IsFalse(x ≡? y)
      l₁ p with 𝐹 ← (x ≡? y) = reflexivity(_≡_)
      l₂ : (Matrix.proj (SquareMatrix.diagMat zero v) (x , y) ≡ zero) ← (Vector.proj v(x) ≡ zero)
      l₂ p with (x ≡? y)
      ... | 𝑇 = p
      ... | 𝐹 = reflexivity(_≡_)
      r : (Matrix.proj (SquareMatrix.diagMat zero v) (x , y) ≡ zero) → (IsFalse(x ≡? y) ∨ (Vector.proj v(x) ≡ zero))
      r p with (x ≡? y)
      ... | 𝑇 = [∨]-introᵣ p
      ... | 𝐹 = [∨]-introₗ [⊤]-intro

  diagMat-element-vector : (Matrix.proj (SquareMatrix.diagMat zero v) (x , y) ≡ Vector.proj v(x)) ↔ ((x ≡ₑ y) ∨ (Vector.proj v(x) ≡ zero))
  diagMat-element-vector {zero = zero}{𝐒 n}{v = v}{x = x}{y = y} =
    [↔]-intro ([↔]-to-[←] [→ₗ][∨][∧]-preserving ([∧]-intro l₁ l₂)) r ⦗ [↔]-transitivity ⦘ᵣ
    [∨]-mapₗ-[↔] ([↔]-symmetry [≡][≡?]-equivalence)
    where
      l₁ : (Matrix.proj (SquareMatrix.diagMat zero v) (x , y) ≡ Vector.proj v(x)) ← IsTrue(x ≡? y)
      l₁ p with 𝑇 ← (x ≡? y) = reflexivity(_≡_)
      l₂ : (Matrix.proj (SquareMatrix.diagMat zero v) (x , y) ≡ Vector.proj v(x)) ← (Vector.proj v(x) ≡ zero)
      l₂ p with (x ≡? y)
      ... | 𝑇 = reflexivity(_≡_)
      ... | 𝐹 = symmetry(_≡_) p
      r : (Matrix.proj (SquareMatrix.diagMat zero v) (x , y) ≡ Vector.proj v(x)) → (IsTrue(x ≡? y) ∨ (Vector.proj v(x) ≡ zero))
      r p with (x ≡? y)
      ... | 𝑇 = [∨]-introₗ [⊤]-intro
      ... | 𝐹 = [∨]-introᵣ (symmetry(_≡_) p)

  scalarMat-element-zero : (Matrix.proj (SquareMatrix.scalarMat zero elem) (x , y) ≡ zero) ↔ ((x ≢ₑ y) ∨ (elem ≡ zero))
  scalarMat-element-zero {zero = zero}{elem = elem}{x = x}{y = y} =
    Matrix.proj (SquareMatrix.scalarMat zero elem) (x , y) ≡ zero             ⇔-[]
    Matrix.proj (SquareMatrix.diagMat zero (Vector.fill elem)) (x , y) ≡ zero ⇔-[ diagMat-element-zero ]
    (x ≢ₑ y) ∨ (Vector.proj (Vector.fill elem)(x) ≡ zero)                     ⇔-[]
    (x ≢ₑ y) ∨ (elem ≡ zero)                                                  ⇔-end

  scalarMat-element-scalar : (Matrix.proj (SquareMatrix.scalarMat zero elem) (x , y) ≡ elem) ↔ ((x ≡ₑ y) ∨ (elem ≡ zero))
  scalarMat-element-scalar {zero = zero}{elem = elem}{x = x}{y = y} =
    Matrix.proj (SquareMatrix.scalarMat zero elem) (x , y) ≡ elem                            ⇔-[]
    Matrix.proj (SquareMatrix.diagMat zero (Vector.fill elem)) (x , y) ≡ Vector.fill elem(x) ⇔-[ diagMat-element-vector ]
    (x ≡ₑ y) ∨ (Vector.proj (Vector.fill elem)(x) ≡ zero)                                    ⇔-[]
    (x ≡ₑ y) ∨ (elem ≡ zero)                                                                 ⇔-end

  map₂-tail : Vector.tail(Vector.map₂(_▫_) v₁ v₂) ≡ Vector.map₂(_▫_) (Vector.tail v₁) (Vector.tail v₂)
  _⊜_.proof (map₂-tail {d = 𝐒(d)}) = reflexivity(_≡_)

  -- TODO: Probably not neccessary : row-tail : ∀{M : Matrix(𝐒(w) , 𝐒(h))(T)}{i} → Vector.tail(Matrix.row {s = (𝐒(w) , 𝐒(h))} M (𝐒(i))) ≡ Matrix.row {s = (w , h)}(Matrix.minor M(𝟎 , 𝟎))(i)

  col-scalarMat-is-indexProject : ∀{false true : T}{i : 𝕟(n)} → (Matrix.col(SquareMatrix.scalarMat {d = n} false true)(i) ≡ Vector.indexProject i true false)
  _⊜_.proof (col-scalarMat-is-indexProject {i = i}) {x} with (i ≡? x)
  ... | 𝑇 = reflexivity(_≡_)
  ... | 𝐹 = reflexivity(_≡_)

  row-scalarMat-is-indexProject : ∀{false true : T}{i : 𝕟(n)} → (Matrix.row(SquareMatrix.scalarMat {d = n} false true)(i) ≡ Vector.indexProject i true false)
  _⊜_.proof (row-scalarMat-is-indexProject {i = i}) {x} with (i ≡? x) | (x ≡? i) | commutativity ⦃ [≡]-equiv ⦄ (_≡?_) {i}{x}
  ... | 𝑇 | 𝑇 | [≡]-intro = reflexivity(_≡_)
  ... | 𝑇 | 𝐹 | ()
  ... | 𝐹 | 𝑇 | ()
  ... | 𝐹 | 𝐹 | [≡]-intro = reflexivity(_≡_)

  module _
    ⦃ oper₁ : BinaryOperator(_+ₛ_) ⦄
    ⦃ oper₂ : BinaryOperator(_⋅ₛ_) ⦄
    ⦃ ident₁ : Identityᵣ(_+ₛ_)(𝟎ₛ) ⦄
    ⦃ ident₂ : Identityᵣ(_⋅ₛ_)(𝟏ₛ) ⦄
    ⦃ absor₂ : Absorberᵣ(_⋅ₛ_)(𝟎ₛ) ⦄
    where
    instance
      postulate matrix-multPattern-identityᵣ : Identityᵣ{T₁ = Matrix(s) T}(Matrix.multPattern(_+ₛ_)(_⋅ₛ_) 𝟎ₛ) (SquareMatrix.scalarMat 𝟎ₛ 𝟏ₛ)
      {-_⊜_.proof (Identityᵣ.proof (matrix-multPattern-identityᵣ ) {M}) {x , y} =
        Matrix.proj (Matrix.multPattern(_+ₛ_)(_⋅ₛ_) 𝟎ₛ M (SquareMatrix.scalarMat 𝟎ₛ 𝟏ₛ)) (x , y)                   🝖[ _≡_ ]-[]
        Vector.foldᵣ(_+ₛ_) 𝟎ₛ (Vector.map₂(_⋅ₛ_) (Matrix.row(M)(y)) (Matrix.col(SquareMatrix.scalarMat 𝟎ₛ 𝟏ₛ)(x))) 🝖[ _≡_ ]-[ congruence₁(Vector.foldᵣ(_+ₛ_) 𝟎ₛ) (congruence₂ᵣ(Vector.map₂(_⋅ₛ_))(Matrix.row M(y)) (col-scalarMat-is-indexProject {false = 𝟎ₛ}{true = 𝟏ₛ}{i = x})) ]
        Vector.foldᵣ(_+ₛ_) 𝟎ₛ (Vector.map₂(_⋅ₛ_) (Matrix.row(M)(y)) (Vector.indexProject x 𝟏ₛ 𝟎ₛ))                 🝖[ _≡_ ]-[ congruence₁(Vector.foldᵣ(_+ₛ_) 𝟎ₛ) (Vector.map₂-indexProject-identityᵣ {v = Matrix.row(M)(y)}{i = x}) ]
        Vector.foldᵣ(_+ₛ_) 𝟎ₛ (Vector.indexProject x (Vector.proj(Matrix.row(M)(y))(x)) 𝟎ₛ)                        🝖[ _≡_ ]-[]
        Vector.foldᵣ(_+ₛ_) 𝟎ₛ (Vector.indexProject x (Matrix.proj M(x , y)) 𝟎ₛ)                                    🝖[ _≡_ ]-[ {!!} ]
        Matrix.proj M(x , y) ⋅ₛ (Vector.foldᵣ(_+ₛ_) 𝟎ₛ (Vector.indexProject x 𝟏ₛ 𝟎ₛ))                              🝖[ _≡_ ]-[ congruence₂ᵣ(_⋅ₛ_)(_) {!!} ]
        Matrix.proj M(x , y) ⋅ₛ 𝟏ₛ                                                                                 🝖[ _≡_ ]-[ identityᵣ(_⋅ₛ_)(𝟏ₛ) ]
        Matrix.proj M(x , y)                                                                                       🝖-end
      -}

  module _
    ⦃ oper₁ : BinaryOperator(_+ₛ_) ⦄
    ⦃ oper₂ : BinaryOperator(_⋅ₛ_) ⦄
    ⦃ ident₁ : Identityₗ(_▫₁_)(id₁) ⦄
    ⦃ ident₂ : Identityₗ(_▫₂_)(id₂) ⦄
    ⦃ absor₂ : Absorberₗ(_⋅ₛ_)(𝟎ₛ) ⦄
    where    
    instance
      postulate matrix-multPattern-identityₗ : Identityₗ{T₂ = Matrix(n , n) T}(Matrix.multPattern(_▫₂_)(_▫₁_) id₁) (SquareMatrix.scalarMat id₂ id₁)

  module _
    ⦃ oper₁ : BinaryOperator(_+ₛ_) ⦄
    ⦃ oper₂ : BinaryOperator(_⋅ₛ_) ⦄
    ⦃ ident₁ : Identity(_▫₁_)(id₁) ⦄
    ⦃ ident₂ : Identity(_▫₂_)(id₂) ⦄
    ⦃ absor₂ : Absorber(_⋅ₛ_)(𝟎ₛ) ⦄
    where
    instance
      postulate matrix-multPattern-identity : Identity{T = Matrix(n , n) T}(Matrix.multPattern(_▫₂_)(_▫₁_) id₁) (SquareMatrix.scalarMat id₂ id₁)

{-
  instance
    matrix-map₂-distributivityᵣ : ⦃ dist : Distributivityᵣ(_▫₁_)(_▫₂_) ⦄ → Distributivityᵣ(Matrix.multPattern(_▫₂_)(_▫₁_) id) (Matrix.map₂{s = s}(_▫₂_))
    _⊜_.proof (Distributivityᵣ.proof (matrix-map₂-distributivityᵣ {_▫₁_} {_▫₂_} {id = id}) {a} {b} {c}) {x , y} =
      Matrix.proj(Matrix.multPattern(_▫₂_) (_▫₁_) id (Matrix.map₂(_▫₂_) a b) c) (x , y) 🝖[ _≡_ ]-[]
      Vector.foldᵣ(_▫₂_) id (Vector.map₂ (_▫₁_) (Matrix.row(Matrix.map₂(_▫₂_) a b)(y)) (Matrix.col(c)(x))) 🝖[ _≡_ ]-[]

      Vector.foldᵣ(_▫₂_) id (Vector.map₂(_▫₁_) (λ x₁ → (Matrix.proj a (x₁ , y)) ▫₂ (Matrix.proj b (x₁ , y))) (λ y₁ → Matrix.proj c (x , y₁))) 🝖[ _≡_ ]-[ {!!} ]
      (Vector.foldᵣ(_▫₂_) id (Vector.map₂ _▫₁_ (λ x₁ → Matrix.proj a (x₁ , y)) (λ y₁ → Matrix.proj c (x , y₁)))) ▫₂ (Vector.foldᵣ(_▫₂_) id (Vector.map₂(_▫₁_) (λ x₁ → Matrix.proj b (x₁ , y)) (λ y₁ → Matrix.proj c (x , y₁)))) 🝖[ _≡_ ]-[]

      (Vector.foldᵣ(_▫₂_) id (Vector.map₂ (_▫₁_) (Matrix.row(a)(y)) (Matrix.col(c)(x)))) ▫₂ (Vector.foldᵣ(_▫₂_) id (Vector.map₂ (_▫₁_) (Matrix.row(b)(y)) (Matrix.col(c)(x)))) 🝖[ _≡_ ]-[]
      Matrix.proj(Matrix.map₂(_▫₂_) (Matrix.multPattern(_▫₂_)(_▫₁_) id a c) (Matrix.multPattern(_▫₂_)(_▫₁_) id b c)) (x , y) 🝖-end
-}
