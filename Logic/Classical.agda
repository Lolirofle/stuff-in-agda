module Logic.Classical where

open import BidirectionalFunction as ↔ using (_$ₗ_ ; _$ᵣ_)
import      Lvl
open import Data
open import Data.Boolean
open import Data.Boolean.Stmt
open import Data.Boolean.Stmt.Proofs using (module IsTrue ; module IsFalse)
open import Data.Boolean.Proofs
open import Data.Either as Either using (_‖_)
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Lang.Instance
open import Logic
open import Logic.Names
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Logic.Predicate
open import Logic.Predicate.Theorems
open import Relator.Equals
open import Syntax.Type
open import Type
open import Type.Properties.Inhabited

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓₒ ℓₒ₁ ℓₒ₂ ℓₒ₃ ℓₗ : Lvl.Level
private variable X Y Z : Type{ℓ}

-- A proposition is behaving classically when excluded middle holds for it.
-- In other words: For the proposition or its negation, if one of them is provable.
-- It could be interpreted as: The proposition is either true or false.
-- In classical logic, this is always the case for any proposition.
-- Note: (∀x. Classical(P(x))) is also called: P is decidable.
module _ (P : Stmt{ℓ}) where
  record Classical : Stmt{ℓ} where -- TODO: Rename to ExcludedMiddle. Define WeakExcludedMiddle = ExcludedMiddle ∘ ¬_ and Classical = ∀ₗ(ExcludedMiddle)
    constructor intro
    field
      ⦃ excluded-middle ⦄ : ExcludedMiddleOn(P)
  excluded-middle = inst-fn Classical.excluded-middle
open Classical ⦃ ... ⦄ hiding (excluded-middle) public

------------------------------------------
-- Classical on predicates.

Classical₁ : (X → Stmt{ℓₗ}) → Stmt
Classical₁(P) = ∀¹(Classical ∘₁ P)

Classical₂ : (X → Y → Stmt{ℓₗ}) → Stmt
Classical₂(P) = ∀²(Classical ∘₂ P)

Classical₃ : (X → Y → Z → Stmt{ℓₗ}) → Stmt
Classical₃(P) = ∀³(Classical ∘₃ P)

------------------------------------------
-- Well-known classical rules.

module _ {P : Stmt{ℓ}} ⦃ classical-P : Classical(P) ⦄ where
  -- Double negation elimination.
  [¬¬]-elim : (¬¬ P) → P
  [¬¬]-elim = [¬¬]-elim-from-excluded-middle (excluded-middle(P))

  -- A double negated proposition is equivalent to the positive.
  double-negation : P ↔ (¬¬ P)
  double-negation = [↔]-intro [¬¬]-elim [¬¬]-intro

  -- The type signature of the "call/cc or "call-with-current-continuation" subroutine in the programming language Scheme.
  -- Also known as: "Peirce's law"
  call-cc-rule : ∀{Q : Stmt{ℓ₂}} → (((P → Q) → P) → P)
  call-cc-rule (pqp) with excluded-middle(P)
  ... | ([∨]-introₗ p ) = p
  ... | ([∨]-introᵣ np) = pqp([⊥]-elim ∘ np)

  -- When the negative implies the positive, thus implying a contradiction, the positive is true.
  -- Also called: "Clavius's Law".
  negative-implies-positive : ((¬ P) → P) → P
  negative-implies-positive npp with excluded-middle(P)
  ... | ([∨]-introₗ p ) = p
  ... | ([∨]-introᵣ np) = npp np

module _ (P : Stmt{ℓ}) ⦃ classical : Classical(P) ⦄ where
  -- Elimination rule for the disjunction in excluded middle.
  excluded-middle-elim : ∀{Q : Stmt{ℓ₂}} → (P → Q) → ((¬ P) → Q) → Q
  excluded-middle-elim pq npq = [∨]-elim pq npq (excluded-middle(P))

------------------------------------------
-- Contraposition rules on implication.

module _ {P : Stmt{ℓ₁}} {Q : Stmt{ℓ₂}} ⦃ classical : Classical(Q) ⦄ where
  -- Contraposition rule in reverse removing negations.
  contrapositiveₗ : (P → Q) ← ((¬ P) ← (¬ Q))
  contrapositiveₗ (npnq) = [¬¬]-elim ∘ (contrapositiveᵣ (npnq)) ∘ [¬¬]-intro

  contrapositive : (P → Q) ↔ ((¬ P) ← (¬ Q))
  contrapositive = [↔]-intro contrapositiveₗ contrapositiveᵣ

  contrapositive-variant2ᵣ : (P ← (¬ Q)) → ((¬ P) → Q)
  contrapositive-variant2ᵣ = [¬¬]-elim ∘₂ (swap _∘_)

module _ {P : Stmt{ℓ₁}} ⦃ classical : Classical(P) ⦄ {Q : Stmt{ℓ₂}} where
  contrapositive-variant2ₗ : ((¬ P) → Q) → (P ← (¬ Q))
  contrapositive-variant2ₗ = contrapositiveₗ ∘ ([¬¬]-intro ∘_)

module _ {P : Stmt{ℓ₁}} ⦃ classic-p : Classical(P) ⦄ {Q : Stmt{ℓ₂}} ⦃ classic-q : Classical(Q) ⦄ where
  contrapositive-variant2 : (P ← (¬ Q)) ↔ ((¬ P) → Q)
  contrapositive-variant2 = [↔]-intro contrapositive-variant2ₗ contrapositive-variant2ᵣ

  one-direction-implication : (P ← Q) ∨ (P → Q)
  one-direction-implication with excluded-middle(P) | excluded-middle(Q)
  one-direction-implication | [∨]-introₗ p  | [∨]-introₗ q  = [∨]-introₗ (const p)
  one-direction-implication | [∨]-introₗ p  | [∨]-introᵣ nq = [∨]-introₗ (const p)
  one-direction-implication | [∨]-introᵣ np | [∨]-introₗ q  = [∨]-introᵣ (const q)
  one-direction-implication | [∨]-introᵣ np | [∨]-introᵣ nq = [∨]-introᵣ ([⊥]-elim ∘ np)

  [¬]-injective : (P ↔ Q) ← ((¬ P) ↔ (¬ Q))
  [¬]-injective ([↔]-intro nqnp npnq) = [↔]-intro (contrapositiveₗ ⦃ classic-p ⦄ npnq) (contrapositiveₗ ⦃ classic-q ⦄ nqnp)

  [↔]-negation : (P ↔ Q) ↔ ((¬ P) ↔ (¬ Q))
  [↔]-negation = [↔]-intro [¬]-injective [¬]-unaryOperator

------------------------------------------
-- XOR.

module _ (P : Stmt{ℓ}) ⦃ classical : Classical(P) ⦄ where
  xor-negation : P ⊕ (¬ P)
  xor-negation with excluded-middle(P)
  ... | [∨]-introₗ p  = [⊕]-introₗ p ([¬¬]-intro p)
  ... | [∨]-introᵣ np = [⊕]-introᵣ np np

module _ {P : Stmt{ℓ₁}} {Q : Stmt{ℓ₂}} where
  classical-from-xorₗ : ⦃ xor : (P ⊕ Q) ⦄ → Classical(P)
  classical-from-xorₗ ⦃ xor ⦄ = intro ⦃ [⊕]-excluded-middleₗ xor ⦄

  classical-from-xorᵣ : ⦃ xor : (P ⊕ Q) ⦄ → Classical(Q)
  classical-from-xorᵣ ⦃ xor ⦄ = intro ⦃ [⊕]-excluded-middleᵣ xor ⦄

------------------------------------------
-- Introduction/elimination rules for Classical when combined with logical connectives.

module _ {P : Stmt{ℓ}} where
  [¬]-classical-intro : ⦃ classical : Classical(P) ⦄ → Classical(¬ P)
  [¬]-classical-intro ⦃ classical-p ⦄ = intro ⦃ proof ⦄ where
    proof : (¬ P) ∨ (¬¬ P)
    proof = Either.swap(Either.mapLeft [¬¬]-intro (excluded-middle(P)))

  excluded-middle-classical-intro : ⦃ _ : Classical(P) ⦄ → Classical(P ∨ (¬ P))
  excluded-middle-classical-intro = intro ⦃ [∨]-introₗ (excluded-middle(P)) ⦄

  -- [¬]-classical-elim : ⦃ _ : Classical(¬ P) ⦄ → Classical(P)
  -- [¬]-classical-elim ⦃ classical ⦄ = intro ⦃ excluded-middle-elim(¬ P) ⦃ classical ⦄ [∨]-introᵣ (nnp ↦ [∨]-introₗ {!!}) ⦄

module _ {P : Stmt{ℓ₁}} {Q : Stmt{ℓ₂}} where
  classical-by-equivalence : (P ↔ Q) → (Classical(P) ↔ Classical(Q))
  classical-by-equivalence (xy) = [↔]-intro (cy ↦ intro ⦃ proofₗ(cy) ⦄) (cx ↦ intro ⦃ proofᵣ(cx) ⦄) where
    proofᵣ : Classical(P) → (Q ∨ (¬ Q))
    proofᵣ (classical-p) with excluded-middle(P) ⦃ classical-p ⦄
    ... | [∨]-introₗ(p)  = [∨]-introₗ([↔]-to-[→] xy p)
    ... | [∨]-introᵣ(nx) = [∨]-introᵣ(nx ∘ ([↔]-to-[←] xy))

    proofₗ : Classical(Q) → (P ∨ (¬ P))
    proofₗ (classical-q) with excluded-middle(Q) ⦃ classical-q ⦄
    ... | [∨]-introₗ(q)  = [∨]-introₗ([↔]-to-[←] xy q)
    ... | [∨]-introᵣ(ny) = [∨]-introᵣ(ny ∘ ([↔]-to-[→] xy))

  instance
    [∧]-classical-intro : ⦃ classical-p : Classical(P) ⦄ → ⦃ classical-q : Classical(Q) ⦄ → Classical(P ∧ Q)
    [∧]-classical-intro ⦃ classical-p ⦄ ⦃ classical-q ⦄ = intro ⦃ proof ⦄ where
      proof : (P ∧ Q) ∨ (¬ (P ∧ Q))
      proof with (excluded-middle(P) , excluded-middle(Q))
      ... | ([∨]-introₗ(p)  , [∨]-introₗ(q))  = [∨]-introₗ([∧]-intro(p)(q))
      ... | ([∨]-introₗ(p)  , [∨]-introᵣ(ny)) = [∨]-introᵣ(xy ↦ ny([∧]-elimᵣ(xy)))
      ... | ([∨]-introᵣ(nx) , [∨]-introₗ(q))  = [∨]-introᵣ(xy ↦ nx([∧]-elimₗ(xy)))
      ... | ([∨]-introᵣ(nx) , [∨]-introᵣ(ny)) = [∨]-introᵣ(xy ↦ nx([∧]-elimₗ(xy)))

  instance
    [∨]-classical-intro : ⦃ classical-p : Classical(P) ⦄ → ⦃ classical-q : Classical(Q) ⦄ → Classical(P ∨ Q)
    [∨]-classical-intro ⦃ classical-p ⦄ ⦃ classical-q ⦄ = intro ⦃ proof ⦄ where
      proof : (P ∨ Q) ∨ (¬ (P ∨ Q))
      proof with (excluded-middle(P) , excluded-middle(Q))
      ... | ([∨]-introₗ(p)  , [∨]-introₗ(q))  = [∨]-introₗ([∨]-introₗ(p))
      ... | ([∨]-introₗ(p)  , [∨]-introᵣ(ny)) = [∨]-introₗ([∨]-introₗ(p))
      ... | ([∨]-introᵣ(nx) , [∨]-introₗ(q))  = [∨]-introₗ([∨]-introᵣ(q))
      ... | ([∨]-introᵣ(nx) , [∨]-introᵣ(ny)) = [∨]-introᵣ(xy ↦ [∨]-elim(nx)(ny) (xy))

  instance
    [→]-classical-intro : ⦃ classical-p : Classical(P) ⦄ → ⦃ classical-q : Classical(Q) ⦄ → Classical(P → Q)
    [→]-classical-intro ⦃ classical-p ⦄ ⦃ classical-q ⦄ = intro ⦃ proof ⦄ where
      proof : (P → Q) ∨ (¬ (P → Q))
      proof with (excluded-middle(P) , excluded-middle(Q))
      ... | ([∨]-introₗ(p)  , [∨]-introₗ(q))  = [∨]-introₗ(const(q))
      ... | ([∨]-introₗ(p)  , [∨]-introᵣ(ny)) = [∨]-introᵣ([¬→][∧]ₗ ([∧]-intro p ny))
      ... | ([∨]-introᵣ(nx) , [∨]-introₗ(q))  = [∨]-introₗ(const(q))
      ... | ([∨]-introᵣ(nx) , [∨]-introᵣ(ny)) = [∨]-introₗ([⊥]-elim ∘ nx)

  instance
    [↔]-classical-intro : ⦃ _ : Classical(P) ⦄ → ⦃ _ : Classical(Q) ⦄ → Classical(P ↔ Q)
    [↔]-classical-intro ⦃ classical-p ⦄ ⦃ classical-q ⦄ = intro ⦃ proof ⦄ where
      proof : (P ↔ Q) ∨ (¬ (P ↔ Q))
      proof with (excluded-middle(P) , excluded-middle(Q))
      ... | ([∨]-introₗ(p)  , [∨]-introₗ(q))  = [∨]-introₗ([↔]-intro (const(p)) (const(q)))
      ... | ([∨]-introₗ(p)  , [∨]-introᵣ(ny)) = [∨]-introᵣ(([¬→][∧]ₗ ([∧]-intro p ny)) ∘ [↔]-to-[→])
      ... | ([∨]-introᵣ(nx) , [∨]-introₗ(q))  = [∨]-introᵣ(([¬→][∧]ₗ ([∧]-intro q nx)) ∘ [↔]-to-[←])
      ... | ([∨]-introᵣ(nx) , [∨]-introᵣ(ny)) = [∨]-introₗ([↔]-intro ([⊥]-elim ∘ ny) ([⊥]-elim ∘ nx))

instance
  [⊤]-classical-intro : Classical(⊤)
  [⊤]-classical-intro = intro ⦃ [∨]-introₗ [⊤]-intro ⦄

instance
  [⊥]-classical-intro : Classical(⊥)
  [⊥]-classical-intro = intro ⦃ [∨]-introᵣ id ⦄

module _ {X : Type{ℓ₁}} ⦃ _ : (◊ X) ⦄ {P : X → Stmt{ℓ₂}} where
  instance
    [∃]-classical-elim : ⦃ _ : Classical(∃ P) ⦄ → ∃(x ↦ Classical(P(x)))
    [∃]-classical-elim ⦃ classical-expx ⦄ with excluded-middle(∃ P)
    ... | [∨]-introₗ(expx)  = [∃]-intro([∃]-witness(expx)) ⦃ intro ⦃ [∨]-introₗ([∃]-proof(expx)) ⦄ ⦄
    ... | [∨]-introᵣ(nexpx) = [∃]-intro([◊]-existence) ⦃ intro ⦃ [∨]-introᵣ([¬∃]-to-[∀¬] (nexpx) {[◊]-existence}) ⦄ ⦄

------------------------------------------
-- ???

module _ {P : Stmt{ℓ}} {Q : Stmt{ℓ₂}} ⦃ classical-Q : Classical(Q) ⦄ where
  -- One direction of the equivalence of implication using conjunction
  [→][∧]ₗ : (P → Q) ← ¬(P ∧ (¬ Q))
  [→][∧]ₗ (nqnp) = [¬¬]-elim ∘ (Tuple.curry(nqnp))
    -- ¬(A ∧ ¬B) → (A → ¬¬B)
    --   ¬(A ∧ (¬ B)) //assumption
    --   ((A ∧ (B → ⊥)) → ⊥) //Definition: (¬)
    --   (A → (B → ⊥) → ⊥) //Tuple.curry
    --   (A → ¬(B → ⊥)) //Definition: (¬)
    --   (A → ¬(¬ B)) //Definition: (¬)

  [→][∧] : (P → Q) ↔ ¬(P ∧ (¬ Q))
  [→][∧] = [↔]-intro [→][∧]ₗ [→][∧]ᵣ

module _ {P : Stmt{ℓ}} ⦃ classical-P : Classical(P) ⦄ where
  -- One direction of the equivalence of implication using disjunction
  [→]-disjunctive-formᵣ : ∀{Q : Stmt{ℓ₂}} → (P → Q) → ((¬ P) ∨ Q)
  [→]-disjunctive-formᵣ (pq) with excluded-middle(P)
  ... | [∨]-introₗ(p)  = [∨]-introᵣ(pq(p))
  ... | [∨]-introᵣ(np) = [∨]-introₗ(np)

  [→]-disjunctive-form : ∀{Q : Stmt{ℓ₂}} → (P → Q) ↔ ((¬ P) ∨ Q)
  [→]-disjunctive-form = [↔]-intro [→]-disjunctive-formₗ [→]-disjunctive-formᵣ

  [→]-from-contrary : ∀{Q : Stmt{ℓ₂}} → (Q → (¬ P) → ⊥) → (Q → P)
  [→]-from-contrary = [¬¬]-elim ∘_

  [¬→]-disjunctive-formᵣ : ∀{Q : Stmt{ℓ₂}} → ((¬ P) → Q) → (P ∨ Q)
  [¬→]-disjunctive-formᵣ npq = excluded-middle-elim P [∨]-introₗ ([∨]-introᵣ ∘ npq)

  [¬→]-disjunctive-form : ∀{Q : Stmt{ℓ₂}} → ((¬ P) → Q) ↔ (P ∨ Q)
  [¬→]-disjunctive-form = [↔]-intro [¬→]-disjunctive-formₗ [¬→]-disjunctive-formᵣ

  -- [↔]-disjunctive-form : ∀{Q : Stmt{ℓ₂}} → (P ↔ Q) ↔ (P ∧ Q) ∨ ((¬ P) ∧ (¬ Q))
  -- [↔]-disjunctive-form = [↔]-intro [↔]-disjunctive-formₗ ?

  module _ {Q : Stmt{ℓ₂}} {R : Stmt{ℓ₃}} where
    [→][∨]-distributivityₗ : (P → (Q ∨ R)) ↔ ((P → Q) ∨ (P → R))
    [→][∨]-distributivityₗ = [↔]-intro [→][∨]-distributivityₗₗ r where
      r : (P → (Q ∨ R)) → ((P → Q) ∨ (P → R))
      r pqr = excluded-middle-elim P ([∨]-elim2 const const ∘ pqr) ([∨]-introₗ ∘ ([⊥]-elim ∘_))

module _ {P : Stmt{ℓ₁}} ⦃ classic-p : Classical(P) ⦄ {Q : Stmt{ℓ₂}} ⦃ classic-q : Classical(Q) ⦄ where
  [¬→][∧]ᵣ : ¬(P → Q) → (P ∧ (¬ Q))
  [¬→][∧]ᵣ = contrapositive-variant2ₗ ⦃ [∧]-classical-intro {P = P}{Q = ¬ Q} ⦃ classical-q = [¬]-classical-intro ⦄ ⦄ ([→][∧]ₗ {Q = Q})

  [¬→][∧] : ¬(P → Q) ↔ (P ∧ (¬ Q))
  [¬→][∧] = [↔]-intro [¬→][∧]ₗ [¬→][∧]ᵣ

classical-topOrBottom : ∀{P : Stmt{ℓ}} → (Classical(P) ↔ TopOrBottom(_↔_)(P))
_⨯_.left  (classical-topOrBottom {P = P}) tb        = intro ⦃ [∨]-elim2 ([↔]-elimₗ [⊤]-intro) [↔]-to-[→] tb ⦄
_⨯_.right (classical-topOrBottom {P = P}) classical = excluded-middle-elim P ⦃ classical ⦄ ([∨]-introₗ ∘ provable-top-equivalence) (([∨]-introᵣ ∘ unprovable-bottom-equivalence))

module _ {P : Stmt{ℓ₁}} ⦃ classic-p : Classical(P) ⦄ {Q : Stmt{ℓ₂}} {R : Stmt{ℓ₃}} ⦃ classic-r : Classical(R) ⦄ where
  -- According to https://math.stackexchange.com/questions/440261/associativity-of-iff , this is unprovable in constructive logic.
  [↔]-associativity : ((P ↔ Q) ↔ R) ↔ (P ↔ (Q ↔ R))
  [↔]-associativity = [↔]-intro (\pqr → ↔.map ↔.rev ↔.id $ᵣ (↔.rev $ᵣ (right (↔.map ↔.rev ↔.id $ᵣ (↔.rev $ᵣ pqr))))) right where
    module _ {ℓ₁ ℓ₂ ℓ₃} {P : Stmt{ℓ₁}} ⦃ classic-p : Classical(P) ⦄ {Q : Stmt{ℓ₂}} {R : Stmt{ℓ₃}} ⦃ classic-r : Classical(R) ⦄ where
      rightₗ : ((P ↔ Q) ↔ R) → (P ← (Q ↔ R))
      rightₗ pqr ([↔]-intro rq qr) with excluded-middle(P) | excluded-middle(R)
      ... | [∨]-introₗ p  | _             = p
      ... | [∨]-introᵣ np | [∨]-introᵣ nr with () ← nr ([↔]-to-[→] pqr ([↔]-intro ([⊥]-elim ∘ nr ∘ qr) ([⊥]-elim ∘ np)))
      ... | [∨]-introᵣ np | [∨]-introₗ r  = [↔]-to-[←] ([↔]-to-[←] pqr r) (rq r)

      rightᵣ = pqr ↦ p ↦ [↔]-intro
        ((pq ↦ [↔]-to-[→] pq p) ∘ [↔]-to-[←] pqr)
        ([↔]-to-[→] pqr ∘ (q ↦ [↔]-intro (const p) (const q)))

      right = pqr ↦ [↔]-intro (rightₗ pqr) (rightᵣ pqr)

------------------------------------------
-- Negation is almost preserved over the conjunction-dijunction dual (De-morgan's laws).

module _ {P : Stmt{ℓ₁}} ⦃ classic-p : Classical(P) ⦄ {Q : Stmt{ℓ₂}} ⦃ classic-q : Classical(Q) ⦄ where
  [¬]-preserves-[∧][∨]ᵣ : ¬(P ∧ Q) → ((¬ P) ∨ (¬ Q))
  [¬]-preserves-[∧][∨]ᵣ npq = [→]-disjunctive-formᵣ {P = P} {Q = ¬ Q} ([→][∧]ₗ ⦃ [¬]-classical-intro ⦄ (npq ∘ (Tuple.mapRight ([¬¬]-elim {P = Q}))))

  [¬]-preserves-[∧][∨] : ¬(P ∧ Q) ↔ ((¬ P) ∨ (¬ Q))
  [¬]-preserves-[∧][∨] = [↔]-intro [¬]-preserves-[∧][∨]ₗ [¬]-preserves-[∧][∨]ᵣ

{- TODO: Organize Logic.Classical.DoubleNegated, and this is already proven in there, though this result is more general.
module _ {P : Stmt{ℓ₁}} {Q : Stmt{ℓ₂}} where
  [¬]-preserves-[∧][∨]ᵣ-weak-excluded-middle : (¬(P ∧ Q) → ((¬ P) ∨ (¬ Q))) ← (Classical(¬ P) ∧ Classical(¬ Q))
  [¬]-preserves-[∧][∨]ᵣ-weak-excluded-middle ([↔]-intro (intro ⦃ pex ⦄) (intro ⦃ qex ⦄)) npq with pex | qex
  ... | [∨]-introₗ np  | [∨]-introₗ nq  = [∨]-introₗ np
  ... | [∨]-introₗ np  | [∨]-introᵣ nnq = [∨]-introₗ np
  ... | [∨]-introᵣ nnp | [∨]-introₗ nq  = [∨]-introᵣ nq
  ... | [∨]-introᵣ nnp | [∨]-introᵣ nnq with () ← (DoubleNegated.[∧]-intro nnp nnq) npq
-}

-- TODO: See TODO directly above
weak-excluded-middle-[¬]-preserves-[∧][∨]ᵣ : (∀{P : Stmt{ℓ}} → Classical(¬ P)) ↔ (∀{P : Stmt{ℓ}}{Q : Stmt{ℓ}} → ¬(P ∧ Q) → ((¬ P) ∨ (¬ Q)))
weak-excluded-middle-[¬]-preserves-[∧][∨]ᵣ = [↔]-intro l r where
  l : (∀{P} → Classical(¬ P)) ← (∀{P}{Q} → ¬(P ∧ Q) → ((¬ P) ∨ (¬ Q)))
  l pres {P} = intro ⦃ pres{P}{¬ P} non-contradiction ⦄
  r : (∀{P} → Classical(¬ P)) → (∀{P}{Q} → ¬(P ∧ Q) → ((¬ P) ∨ (¬ Q)))
  r wem {P}{Q} npq with excluded-middle(¬ P) ⦃ wem ⦄ | excluded-middle(¬ Q) ⦃ wem ⦄
  ... | [∨]-introₗ np  | [∨]-introₗ nq  = [∨]-introₗ np
  ... | [∨]-introₗ np  | [∨]-introᵣ nnq = [∨]-introₗ np
  ... | [∨]-introᵣ nnp | [∨]-introₗ nq  = [∨]-introᵣ nq
  ... | [∨]-introᵣ nnp | [∨]-introᵣ nnq = [∨]-introₗ (p ↦ nnq(q ↦ npq([∧]-intro p q)))

------------------------------------------
-- Predicate logic.

module _ {P : Stmt{ℓ}} ⦃ classical-P : Classical(P) ⦄ {X : Type{ℓ₂}} ⦃ pos@(intro ⦃ x ⦄) : (◊ X) ⦄ {Q : X → Stmt{ℓ₃}} where
  [∃]-unrelatedᵣ-[→]ₗ : ∃(x ↦ (P → Q(x))) ← (P → ∃(x ↦ Q(x)))
  [∃]-unrelatedᵣ-[→]ₗ pexqx with excluded-middle(P)
  ... | ([∨]-introₗ p)  = [∃]-map-proof (const) (pexqx(p))
  ... | ([∨]-introᵣ np) = [∃]-intro(x) ⦃ [⊥]-elim {P = Q(x)} ∘ np ⦄

  [∃]-unrelatedᵣ-[→] : ∃(x ↦ (P → Q(x))) ↔ (P → ∃(x ↦ Q(x)))
  [∃]-unrelatedᵣ-[→] = [↔]-intro [∃]-unrelatedᵣ-[→]ₗ [∃]-unrelatedᵣ-[→]ᵣ

module _ {X : Type{ℓ₁}} ⦃ _ : (◊ X) ⦄ {P : X → Stmt{ℓ₂}} ⦃ classical-expx : Classical(∃ P) ⦄ {Q : X → Stmt{ℓ₃}} where
  [∃][←]-distributivity : ∃(x ↦ (P(x) → Q(x))) ← (∃(x ↦ P(x)) → ∃(x ↦ Q(x)))
  [∃][←]-distributivity (expx-exqx) =
      (([∃]-map-proof (\{x} → proof ↦ proof{x})
        (([∃]-map-proof (\{x} → [↔]-to-[←] ([∀]-unrelatedₗ-[→] {X = X}{P}{Q(x)}))
          (([∃]-unrelatedᵣ-[→]ₗ ⦃ classical-expx ⦄
            (expx-exqx :of: (∃(x ↦ P(x)) → ∃(x ↦ Q(x))))
          )            :of: (∃(x ↦ (∃(x ↦ P(x)) → Q(x)))))
        )              :of: (∃(x ↦ ∀ₗ(y ↦ (P(y) → Q(x))))))
      )                :of: (∃(x ↦ (P(x) → Q(x)))))

{-
module _ {X : Type{ℓ₁}} ⦃ _ : (◊ X) ⦄ {P : X → Stmt{ℓ₂}} where
  [¬∀¬]-to-[∃] : (∃ P) ← ¬(∀ₗ(¬_ ∘ P))
  [¬∀¬]-to-[∃] x = {!!} -- TODO: When is this true?

  [∃]-classical-intro : ⦃ _ : Classical(∀ₗ P) ⦄ ⦃ _ : Classical(∀ₗ(¬_ ∘ P)) ⦄ → Classical(∃ P)
  Classical.excluded-middle ([∃]-classical-intro ⦃ classical-pa ⦄ ⦃ classical-npa ⦄) with excluded-middle(∀ₗ P) | excluded-middle(∀ₗ(¬_ ∘ P))
  ... | [∨]-introₗ ap  | [∨]-introₗ nap  with () ← nap(ap {[◊]-existence})
  ... | [∨]-introₗ ap  | [∨]-introᵣ nanp = [∨]-introₗ ([∃]-intro [◊]-existence ⦃ ap ⦄)
  ... | [∨]-introᵣ npa | [∨]-introₗ nap  = [∨]-introᵣ ([∀¬]-to-[¬∃] nap)
  ... | [∨]-introᵣ npa | [∨]-introᵣ nanp = [∨]-introₗ ([¬∀¬]-to-[∃] nanp)
-}

-- TODO: Maybe try to get rid of the second instance assumption? Idea: Only [¬¬]-elim is needed for that one, so if possible and true, prove: (∀{x} → Classic(P(x)) → P(x)) → (Classic(∃ P) → (∃ P)). No, that is probably not true
module _ {X : Type{ℓ₁}}{P : X → Stmt{ℓ₂}} ⦃ classical-proof1 : ∀{x} → Classical(P(x)) ⦄ ⦃ classical-proof2 : Classical(∃(¬_ ∘ P)) ⦄ where
  [¬∀]-to-[∃¬] : ∃(x ↦ ¬(P(x))) ← ¬(∀ₗ(x ↦ P(x)))
  [¬∀]-to-[∃¬] (naxpx) =
    ([¬¬]-elim ⦃ classical-proof2 ⦄
      ([¬]-intro {P = ¬ ∃(x ↦ ¬(P(x)))} (nexnpx ↦
        (naxpx
          ([∀][→]-distributivity {X = X}{¬¬_ ∘ P}
            ((\{x} → [¬¬]-elim ⦃ classical-proof1{x} ⦄) :of: ∀ₗ(x ↦ (¬¬ P(x) → P(x))))
            ([¬∃]-to-[∀¬] (nexnpx)                      :of: ∀ₗ(x ↦ ¬¬ P(x)))
          :of: ∀ₗ(x ↦ P(x)))
        ) :of: ⊥
      ) :of: (¬¬ ∃(x ↦ ¬ P(x))))
    ) :of: ∃(x ↦ ¬ P(x))
    -- ¬∀x. P(x)
    -- • ¬∃x. ¬P(x)
    --   ¬∃x. ¬P(x)
    --   ⇒ ∀x. ¬¬P(x)
    --   ⇒ ∀x. P(x)
    --   ⇒ ⊥
    -- ⇒ ¬¬∃x. ¬P(x)
    -- ⇒ ∃x. ¬P(x)

  [∃]-unrelatedₗ-[→]ₗ : ⦃ _ : ◊ X ⦄ → ⦃ _ : Classical(∀ₗ P) ⦄ → ∀{Q : Stmt{ℓ₃}} → ∃(x ↦ (P(x) → Q)) ← (∀ₗ(x ↦ P(x)) → Q)
  [∃]-unrelatedₗ-[→]ₗ ⦃ pos-x ⦄ ⦃ classical-axpx ⦄ {Q} axpxq with excluded-middle(∀ₗ P)
  ... | ([∨]-introₗ axpx)  = [∃]-intro([◊]-existence) ⦃ const(axpxq (axpx)) ⦄
  ... | ([∨]-introᵣ naxpx) = [∃]-map-proof ([⊥]-elim ∘_) ([¬∀]-to-[∃¬] (naxpx))
  -- (∀x. P(x)) → Q
  -- • ∀x. P(x)
  --   ∀x. P(x)
  --   ⇒ ∀x. P(x)
  --   ⇒ Q
  --   ⇒ P(a) → Q
  --   ⇒ ∃x. P(x) → Q
  -- • ¬∀x. P(x)
  --   ¬∀x. P(x)
  --   ⇒ ∃x. ¬P(x)
  --   ⇒ ∃x. P(x) → Q

  -- Also known as: Drinker paradox
  drinker-ambiguity : ⦃ _ : ◊ X ⦄ → ⦃ _ : Classical(∀ₗ P) ⦄ → ∃(x ↦ (P(x) → ∀{y} → P(y)))
  drinker-ambiguity = [∃]-map-proof (\pxap px {y} → pxap px {y}) ([∃]-unrelatedₗ-[→]ₗ id)

  drinker-ambiguity-equiv : ⦃ _ : Classical(∀ₗ P) ⦄ → ((◊ X) ↔ ∃(x ↦ (P(x) → ∀{y} → P(y))))
  drinker-ambiguity-equiv ⦃ classical-axpx ⦄ =
    [↔]-intro
      (\ex → intro ⦃ [∃]-witness ex ⦄)
      (\pos-x → drinker-ambiguity ⦃ pos-x ⦄ ⦃ classical-axpx ⦄)
