open import Type
open import Structure.Relator
open import Structure.Setoid renaming (_≡_ to _≡ₑ_)

module Structure.Set.ZFC.Oper {ℓₛ ℓₗ ℓₑ} {S : Type{ℓₛ}} ⦃ equiv : Equiv{ℓₑ}(S) ⦄ (_∈_ : S → S → Type{ℓₗ}) ⦃ [∈]-binaryRelator : BinaryRelator(_∈_) ⦄ where

open import Functional using (id ; _∘₂_)
open import DependentFunctional using (_∘_)
import      Lvl
open import Logic.Predicate
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Properties
open import Structure.Relator.Proofs renaming ([≡]-binaryRelator to [≡ₑ]-binaryRelator)
open import Structure.Set.ZFC(_∈_) ⦃ [∈]-binaryRelator ⦄
import      Structure.Set.Names
open import Syntax.Function
open import Syntax.Implication

open        Structure.Set.Names.From-[∈] (_∈_)
open        Structure.Set.Names.Relations (_∈_)
open        Structure.Set.Names.One                     (_∈_)
open        Structure.Set.Names.Two                     (_∈_)(_∈_)
open        Structure.Set.Names.TwoDifferent            (_∈_)(_∈_)
open        Structure.Set.Names.TwoSame                 (_∈_)(_∈_)
open        Structure.Set.Names.Three                   (_∈_)(_∈_)(_∈_)
open        Structure.Set.Names.ThreeNestedTwoDifferent (_∈_)
open        Structure.Set.Names.ThreeTwoNested          (_∈_)(_∈_)(_∈_)
open import Structure.Set.Quantifiers(_∈_)
open import Structure.Set.Quantifiers.Proofs(_∈_) ⦃ [∈]-binaryRelator ⦄

private variable ℓ : Lvl.Level
private variable A B C D E N a b c d e x y z As : S
private variable P : S → Type{ℓ}

module _ ⦃ zfc : ZFC ⦄ where
  open ZFC(zfc)

  infixl 3001 _∩_
  infixl 3002 _⨯_ _∖_

  -- Intersection operator.
  -- Constructs a set which consists of elements which are in both LHS and RHS.
  _∩_ : S → S → S
  a ∩ b = filter(_∈ b) ⦃ BinaryRelator-unary₁(_∈_) ⦄ a

  -- "Without"-operator.
  -- Constructs a set which consists of elements which are in LHS, but not RHS.
  _∖_ : S → S → S
  a ∖ b = filter(_∉ b) ⦃ [¬]-unaryRelator ⦃ rel-P = BinaryRelator-unary₁(_∈_) ⦄ ⦄ a

  -- Intersection over arbitrary sets.
  -- Constructs a set which consists of elements which are in all of the specified sets.
  ⋂ : S → S
  ⋂(As) = filter(a ↦ (∀ₛ(As) (a ∈_))) ⦃ [∀]-unaryRelator ⦃ rel-P = [→]-unaryRelator ⦃ rel-Q = BinaryRelator-unary₁(_∈_) ⦄ ⦄ ⦄ (⋃(As))

  -- Tuple value.
  -- An ordered pair of values.
  _,_ : S → S → S
  (a , b) = pair(singleton a) (pair a b)

  -- Set product (Set of tuples) (Cartesian product).
  _⨯_ : S → S → S
  A ⨯ B = filter(t ↦ ∃ₛ(A)(a ↦ ∃ₛ(B)(b ↦ t ≡ₑ (a , b)))) ⦃ [∃ₛ]-unaryRelator ⦃ rel-P = [∃ₛ]-unaryRelator ⦃ rel-P = BinaryRelator-unary₁(_≡ₑ_) ⦃ [≡ₑ]-binaryRelator ⦄ ⦄ ⦄ ⦄ (℘(℘(A ∪ B)))

  identityPair : S → S
  identityPair(D) = filter(xy ↦ ∃(a ↦ xy ≡ₑ (a , a))) ⦃ [∃]-unaryRelator ⦃ rel-P = BinaryRelator-unary₁(_≡ₑ_) ⦃ [≡ₑ]-binaryRelator ⦄ ⦄ ⦄ (D ⨯ D)

  -- Quotient set.
  -- The set of equivalence classes.
  _/_ : S → (_▫_ : S → S → Type{ℓ}) ⦃ rel : BinaryRelator(_▫_) ⦄ → S
  (a / (_▫_)) ⦃ rel ⦄ = filter(aₛ ↦ ∀ₛ(aₛ)(x ↦ ∀ₛ(aₛ)(x ▫_))) ⦃ BinaryRelator-unary₁(_) ⦃ [∀ₛ]-binaryRelator {P = \x A _ → ∀ₛ(A) (x ▫_)} ⦃ rel-P = [∀ₛ]-binaryRelator ⦃ rel-P = const-binaryRelator ⦄ ⦄ ⦄ {∅} ⦄ (℘(a))

  -- Equivalence class.
  -- The set of elements which are equivalent to the specified one.
  [_of_,_] : S → S → (_▫_ : S → S → Type{ℓ}) ⦃ rel : BinaryRelator(_▫_) ⦄ → S
  [ x of a , (_▫_) ] = filter(x ▫_) ⦃ BinaryRelator-unary₂ _ ⦄ a

  -- The unmap of a set.
  -- The set of elements in the domain X when applied to a function gives an element in Y.
  -- Or: The inverse image of the function on the set.
  -- Or: The pre-image of the function on the set.
  -- Note:
  --   The domain is neccessary because a class function's domain is not neccesarily a set.
  --   For example: `const(x): Domain → Domain` for any (x: Domain) is a class function for which its domain is not a set.
  --   This is because const is defined for all objects in `Domain`, so if a set would have to have all objects in `Domain`, it has to be the universal set, but there is no universal set.
  unmap : S → (f : S → S) ⦃ func : Function(f) ⦄ → S → S
  unmap(X) f(Y) = filter(x ↦ f(x) ∈ Y) ⦃ [∘]-unaryRelator {P = _∈ Y} ⦃ BinaryRelator-unary₁ _ ⦄ ⦄ X

  [∩]-inclusion : IntersectMembership(_∩_)
  [∩]-inclusion {A = A}{B = B}{x = x} =
    (x ∈ (A ∩ B))                     ⇔-[]
    x ∈ filter(_∈ B) ⦃ _ ⦄ A          ⇔-[ restricted-comprehension ⦃ _ ⦄ ]
    (x ∈ A) ∧ (x ∈ B)                 ⇔-end

  [∖]-inclusion : WithoutMembership(_∖_)
  [∖]-inclusion {A = A}{B = B}{x = x} =
    (x ∈ (A ∖ B))                     ⇔-[]
    x ∈ filter(_∉ B) ⦃ _ ⦄ A          ⇔-[ restricted-comprehension ⦃ _ ⦄ ]
    (x ∈ A) ∧ (x ∉ B)                 ⇔-end

  intersection : BigIntersectionMembershipWithEmpty(⋂)
  intersection {A = A}{x = x} =
    (x ∈ filter(a ↦ ∀ₛ(A)(a ∈_)) ⦃ _ ⦄ (⋃ A)) ⇔-[ restricted-comprehension ⦃ _ ⦄ ]
    (x ∈ ⋃ A) ∧ ∀ₛ(A)(x ∈_)                   ⇔-[ [∧]-map-[↔] union [↔]-reflexivity ]
    ∃(a ↦ (a ∈ A) ∧ (x ∈ a)) ∧ ∀ₛ(A)(x ∈_)    ⇔-end

  [⨯]-inclusion : (x ∈ (A ⨯ B)) ↔ ∃ₛ(A)(a ↦ ∃ₛ(B)(b ↦ x ≡ₑ (a , b)))
  [⨯]-inclusion {x = x}{A = A}{B = B} =
    (x ∈ (A ⨯ B))                                                          ⇔-[]
    x ∈ filter(t ↦ ∃ₛ(A)(a ↦ ∃ₛ(B)(b ↦ t ≡ₑ (a , b)))) ⦃ _ ⦄ (℘(℘(A ∪ B))) ⇔-[ restricted-comprehension ⦃ _ ⦄ ]
    (x ∈ ℘(℘(A ∪ B))) ∧ ∃ₛ(A)(a ↦ ∃ₛ(B)(b ↦ (x ≡ₑ (a , b))))               ⇔-[ [↔]-intro (p ↦ [∧]-intro (l p) p) [∧]-elimᵣ ]
    ∃ₛ(A)(a ↦ ∃ₛ(B)(b ↦ x ≡ₑ (a , b)))                                     ⇔-end
    where
      tuple-superset : (a ∈ A) → (b ∈ B) → ((a , b) ⊆ ℘(A ∪ B))
      tuple-superset pa pb = pair-superset
        ([↔]-to-[←] power (singleton-superset
          ([↔]-to-[←] [∪]-inclusion ([∨]-introₗ pa))
        ))
        ([↔]-to-[←] power (pair-superset
          ([↔]-to-[←] union ([∃]-intro A ⦃ [∧]-intro pair-contains-left  pa ⦄))
          ([↔]-to-[←] union ([∃]-intro B ⦃ [∧]-intro pair-contains-right pb ⦄))
        ))

      l =
        ∃ₛ(A)(a ↦ ∃ₛ(B)(b ↦ x ≡ₑ (a , b)))                     ⇒-[ [∃]-map-proof ([∧]-map id ([∃]-map-proof ([∧]-map id ([↔]-to-[→] set-extensionality)))) ]
        ∃ₛ(A)(a ↦ ∃ₛ(B)(b ↦ x ≡ (a , b)))                      ⇒-[ [∃]-map-proof ([∧]-map id ([∃]-map-proof ([∧]-map id (sub₂(_≡_)(_⊆_))))) ]
        ∃ₛ(A)(a ↦ ∃ₛ(B)(b ↦ x ⊆ (a , b)))                      ⇒-[]
        ∃ₛ(A)(a ↦ ∃ₛ(B)(b ↦ x ⊆ pair(singleton a) (pair a b))) ⇒-[ (\([∃]-intro _ ⦃ [∧]-intro pa ([∃]-intro _ ⦃ [∧]-intro pb sub ⦄) ⦄) {y} → transitivity(_⊆_) sub (tuple-superset pa pb) {y}) ]
        x ⊆ ℘(A ∪ B)                                           ⇒-[ [↔]-to-[←] power ]
        x ∈ ℘(℘(A ∪ B))                                        ⇒-end

  instance
    ⋂-function : Function(⋂)
    Function.congruence ⋂-function {x = As}{y = Bs} AsBs = filter-function ⦃ _ ⦄ ⦃ _ ⦄ p (congruence₁(⋃) AsBs) where
      p : ∀{x} → (∀{A} → (A ∈ As) → (x ∈ A)) ↔ (∀{B} → (B ∈ Bs) → (x ∈ B))
      p = [↔]-intro (_∘ (substitute₂-₂ᵣ(_∈_)(_) AsBs)) (_∘ (substitute₂-₂ᵣ(_∈_)(_) (symmetry(_≡ₑ_) AsBs)))

  instance
    ∪-operator : BinaryOperator(_∪_)
    BinaryOperator.congruence ∪-operator = congruence₁(⋃) ∘₂ congruence₂(pair)

  instance
    ∩-operator : BinaryOperator(_∩_)
    BinaryOperator.congruence ∩-operator xy1 xy2 = filter-function ⦃ _ ⦄ ⦃ _ ⦄ ([↔]-to-[→] set-extensionality xy2) xy1

  instance
    ∖-operator : BinaryOperator(_∖_)
    BinaryOperator.congruence ∖-operator xy1 xy2 = filter-function ⦃ _ ⦄ ⦃ _ ⦄ ([¬]-unaryOperator ([↔]-to-[→] set-extensionality xy2)) xy1

  instance
    [,]-operator : BinaryOperator(_,_)
    BinaryOperator.congruence [,]-operator xy1 xy2 = congruence₂(pair) (congruence₁(singleton) xy1) (congruence₂(pair) xy1 xy2)

