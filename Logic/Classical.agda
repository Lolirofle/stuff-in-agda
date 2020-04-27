module Logic.Classical where

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
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Logic.Predicate
open import Logic.Predicate.Theorems
open import Relator.Equals
open import Type
open import Type.Empty

private variable ℓ ℓ₁ ℓ₂ ℓ₃ : Lvl.Level

-- A proposition is behaving classically when excluded middle holds for it.
-- In other words: For the proposition or its negation, if one of them is provable.
-- It could be interpreted as: The proposition is either true or false.
-- In classical logic, this is always the case for any proposition.
-- Sometimes (∀x. Classical(P(x))) is called: P is decidable
module _ (P : Stmt{ℓ}) where
  record Classical : Stmt{ℓ} where
    constructor intro
    field
      ⦃ excluded-middle ⦄ : P ∨ (¬ P)

    decide : Bool
    decide = Either.isLeft(excluded-middle)

    -- TODO: Maybe use the generalized functions in Data.Boolean.Proofs to implement these. The either-bool-* functions.
    decide-true : P ↔ (decide ≡ 𝑇)
    decide-true with excluded-middle | bivalence{decide}
    decide-true | [∨]-introₗ p  | [∨]-introₗ t = [↔]-intro (const p) (const t)
    decide-true | [∨]-introᵣ np | [∨]-introᵣ f = [↔]-intro (\()) (empty ∘ np)

    decide-false : (¬ P) ↔ (decide ≡ 𝐹)
    decide-false with excluded-middle | bivalence{decide}
    decide-false | [∨]-introₗ p  | [∨]-introₗ t = [↔]-intro (\()) (np ↦ empty(np p))
    decide-false | [∨]-introᵣ np | [∨]-introᵣ f = [↔]-intro (const np) (const f)

    decide-is-true : P ↔ IsTrue(decide)
    decide-is-true = [↔]-transitivity decide-true ([↔]-symmetry IsTrue.is-𝑇)

    decide-is-false : (¬ P) ↔ IsFalse(decide)
    decide-is-false = [↔]-transitivity decide-false ([↔]-symmetry IsFalse.is-𝐹)

    decide-excluded-middle : (P ∧ (decide ≡ 𝑇)) ∨ ((¬ P) ∧ (decide ≡ 𝐹))
    decide-excluded-middle = [∨]-elim2 (p ↦ [∧]-intro p ([↔]-to-[→] decide-true p)) (np ↦ [∧]-intro np ([↔]-to-[→] decide-false np)) excluded-middle

    module _ {T : Type{ℓ₁}} {x y : T} {Q : T → Type{ℓ₂}} where
      decide-if-intro : (P → Q(x)) → ((¬ P) → Q(y)) → Q(if decide then x else y)
      decide-if-intro pq npq = if-intro{x = x}{y = y}{P = Q}{B = decide} (pq ∘ [↔]-to-[←] decide-true) (npq ∘ [↔]-to-[←] decide-false)

    -- Double negation elimination
    [¬¬]-elim : (¬¬ P) → P
    [¬¬]-elim = [¬¬]-elim-from-excluded-middle (excluded-middle)

    -- Contraposition rule in reverse
    contrapositiveₗ : ∀{Q : Stmt{ℓ₂}} → (Q → P) ← ((¬ Q) ← (¬ P))
    contrapositiveₗ (nqnp) = [¬¬]-elim ∘ (contrapositiveᵣ (nqnp)) ∘ [¬¬]-intro
      -- (¬ X) ← (¬ Y)
      -- (¬ Y) → (¬ X)
      -- (Y → ⊥) → (X → ⊥)
      -- (Y → ⊥) → X → ⊥
      -- X → (Y → ⊥) → ⊥
      -- X → ((Y → ⊥) → ⊥)
      -- X → (¬ (Y → ⊥))
      -- X → (¬ (¬ Y))

    -- One direction of the equivalence of implication using disjunction
    [→]-disjunctive-formᵣ : ∀{Q : Stmt{ℓ₂}} → (P → Q) → ((¬ P) ∨ Q)
    [→]-disjunctive-formᵣ (pq) with excluded-middle
    ... | [∨]-introₗ(p)  = [∨]-introᵣ(pq(p))
    ... | [∨]-introᵣ(np) = [∨]-introₗ(np)

    -- One direction of the equivalence of implication using conjunction
    [→][∧]ₗ : ∀{Q : Stmt{ℓ₂}} → (Q → P) ← ¬(Q ∧ (¬ P))
    [→][∧]ₗ (nqnp) = [¬¬]-elim ∘ (Tuple.curry(nqnp))
      -- ¬(A ∧ ¬B) → (A → ¬¬B)
      --   ¬(A ∧ (¬ B)) //assumption
      --   ((A ∧ (B → ⊥)) → ⊥) //Definition: (¬)
      --   (A → (B → ⊥) → ⊥) //Tuple.curry
      --   (A → ¬(B → ⊥)) //Definition: (¬)
      --   (A → ¬(¬ B)) //Definition: (¬)

    [→]-from-contrary : ∀{Q : Stmt{ℓ₂}} → (Q → (¬ P) → ⊥) → (Q → P)
    [→]-from-contrary = [¬¬]-elim ∘_

    -- The type signature of the "call/cc or "call-with-current-continuation" subroutine in the programming language Scheme
    -- Also known as: "Peirce's law"
    call-cc : ∀{Q : Stmt{ℓ₂}} → (((P → Q) → P) → P)
    call-cc (pqp) with excluded-middle
    ... | ([∨]-introₗ p ) = p
    ... | ([∨]-introᵣ np) = pqp([⊥]-elim ∘ np)

    contrapositive-variantₗ : ∀{Q : Stmt{ℓ₂}} → ((¬ P) → Q) → (P ← (¬ Q))
    contrapositive-variantₗ {Q = Q} npq nq = nqnp(nq) where
      npnnq : (¬ P) → (¬¬ Q)
      npnnq = [¬¬]-intro ∘ npq

      nqnp : (¬ Q) → P
      nqnp = contrapositiveₗ (npnnq)

    -- Also known as: "Clavius's Law"
    negative-implies-positive : ((¬ P) → P) → P
    negative-implies-positive npp with excluded-middle
    ... | ([∨]-introₗ p ) = p
    ... | ([∨]-introᵣ np) = npp np

    [∃]-unrelatedᵣ-[→]ₗ : ∀{X : Type{ℓ₂}} → ⦃ _ : ◊ X ⦄ → ∀{Q : X → Stmt{ℓ₃}} → ∃(x ↦ (P → Q(x))) ← (P → ∃(x ↦ Q(x)))
    [∃]-unrelatedᵣ-[→]ₗ {X} ⦃ intro ⦃ x ⦄ ⦄ {Q} = l where
      l : ∃(x ↦ (P → Q(x))) ← (P → ∃(x ↦ Q(x)))
      l(pexqx) with excluded-middle
      ... | ([∨]-introₗ p)  = [∃]-map-proof (const) (pexqx(p))
      ... | ([∨]-introᵣ np) = [∃]-intro(x) ⦃ ([⊥]-elim{P = Q(x)}) ∘ np ⦄

  excluded-middle = inst-fn Classical.excluded-middle
  decide          = inst-fn Classical.decide
open Classical ⦃ ... ⦄ hiding (excluded-middle ; decide ; decide-true ; decide-false) public

module _ {P : Stmt{ℓ}} where
  instance
    [¬]-classical-intro : ⦃ _ : Classical(P) ⦄ → Classical(¬ P)
    [¬]-classical-intro ⦃ classical-p ⦄ = intro ⦃ proof ⦄ where
      proof : (¬ P) ∨ (¬¬ P)
      proof = Either.swap(Either.mapLeft [¬¬]-intro (excluded-middle(P)))

module _ {P : Stmt{ℓ₁}} {Q : Stmt{ℓ₂}} where
  {- TODO: Seems impossible to get the q
  instance
    [∧]-classical-elimₗ : ⦃ _ : Classical(P ∧ Q) ⦄ → Classical(P)
    [∧]-classical-elimₗ {P}{Q} ⦃ classical-xy ⦄ = classical-intro (proof) where
      proof : P ∨ (¬ P)
      proof with excluded-middle ⦃ classical-xy ⦄
      ... | [∨]-introₗ(xy)  = [∨]-introₗ([∧]-elimₗ(xy))
      ... | [∨]-introᵣ(nxy) = [∨]-introᵣ(p ↦ nxy([∧]-intro(p)(q)))
  -}

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
    [∧]-classical-intro : ⦃ _ : Classical(P) ⦄ → ⦃ _ : Classical(Q) ⦄ → Classical(P ∧ Q)
    [∧]-classical-intro ⦃ classical-p ⦄ ⦃ classical-q ⦄ = intro ⦃ proof ⦄ where
      proof : (P ∧ Q) ∨ (¬ (P ∧ Q))
      proof with (excluded-middle(P) , excluded-middle(Q))
      ... | ([∨]-introₗ(p)  , [∨]-introₗ(q))  = [∨]-introₗ([∧]-intro(p)(q))
      ... | ([∨]-introₗ(p)  , [∨]-introᵣ(ny)) = [∨]-introᵣ(xy ↦ ny([∧]-elimᵣ(xy)))
      ... | ([∨]-introᵣ(nx) , [∨]-introₗ(q))  = [∨]-introᵣ(xy ↦ nx([∧]-elimₗ(xy)))
      ... | ([∨]-introᵣ(nx) , [∨]-introᵣ(ny)) = [∨]-introᵣ(xy ↦ nx([∧]-elimₗ(xy)))

  instance
    [∨]-classical-intro : ⦃ _ : Classical(P) ⦄ → ⦃ _ : Classical(Q) ⦄ → Classical(P ∨ Q)
    [∨]-classical-intro ⦃ classical-p ⦄ ⦃ classical-q ⦄ = intro ⦃ proof ⦄ where
      proof : (P ∨ Q) ∨ (¬ (P ∨ Q))
      proof with (excluded-middle(P) , excluded-middle(Q))
      ... | ([∨]-introₗ(p)  , [∨]-introₗ(q))  = [∨]-introₗ([∨]-introₗ(p))
      ... | ([∨]-introₗ(p)  , [∨]-introᵣ(ny)) = [∨]-introₗ([∨]-introₗ(p))
      ... | ([∨]-introᵣ(nx) , [∨]-introₗ(q))  = [∨]-introₗ([∨]-introᵣ(q))
      ... | ([∨]-introᵣ(nx) , [∨]-introᵣ(ny)) = [∨]-introᵣ(xy ↦ [∨]-elim(nx)(ny) (xy))

  instance
    [→]-classical-intro : ⦃ _ : Classical(P) ⦄ → ⦃ _ : Classical(Q) ⦄ → Classical(P → Q)
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
  [⊤]-classical-intro = intro ⦃ [∨]-introₗ ([⊤]-intro) ⦄ where

instance
  [⊥]-classical-intro : Classical(⊥)
  [⊥]-classical-intro = intro ⦃ [∨]-introᵣ (id) ⦄ where

module _ {X : Type{ℓ₁}} ⦃ _ : (◊ X) ⦄ {P : X → Stmt{ℓ₂}} where
  instance
    [∃]-classical-elim : ⦃ _ : Classical(∃ P) ⦄ → ∃(x ↦ Classical(P(x)))
    [∃]-classical-elim ⦃ classical-expx ⦄ with excluded-middle(∃ P)
    ... | [∨]-introₗ(expx)  = [∃]-intro([∃]-witness(expx)) ⦃ intro ⦃ [∨]-introₗ([∃]-proof(expx)) ⦄ ⦄
    ... | [∨]-introᵣ(nexpx) = [∃]-intro([◊]-existence) ⦃ intro ⦃ [∨]-introᵣ([¬∃]-to-[∀¬] (nexpx) {[◊]-existence}) ⦄ ⦄

module _ {P : Stmt{ℓ₁}} {Q : Stmt{ℓ₂}} ⦃ classic-p : Classical(P) ⦄ ⦃ classic-q : Classical(Q) ⦄ where
  [¬][∧]ₗ : ((¬ P) ∨ (¬ Q)) ← (¬ (P ∧ Q))
  [¬][∧]ₗ npq =
    [→]-disjunctive-formᵣ {P = P} ⦃ classic-p ⦄ {Q = ¬ Q} ([→][∧]ₗ ⦃ [¬]-classical-intro ⦃ classic-q ⦄ ⦄ (npq ∘ (Tuple.mapRight ([¬¬]-elim ⦃ classic-q ⦄))))
    -- ((P ∧ Q) → ⊥) → ((P → ⊥) ∨ (Q → ⊥))
    -- ¬((P ∧ Q) → ⊥) ← ¬((P → ⊥) ∨ (Q → ⊥))

  -- TODO: Is this provable constructivelq? Doesn't seem like it?
  [¬→][∧]ᵣ : ¬(P → Q) → (P ∧ (¬ Q))
  [¬→][∧]ᵣ = contrapositive-variantₗ ⦃ [∧]-classical-intro ⦃ classic-p ⦄ ⦃ [¬]-classical-intro ⦃ classic-q ⦄ ⦄ ⦄ ([→][∧]ₗ ⦃ classic-q ⦄)

  [↔]-negationₗ : (P ↔ Q) ← ((¬ P) ↔ (¬ Q))
  [↔]-negationₗ ([↔]-intro nqnp npnq) = [↔]-intro (contrapositiveₗ ⦃ classic-p ⦄ npnq) (contrapositiveₗ ⦃ classic-q ⦄ nqnp)

  [↔]-one-direction : (P ← Q) ∨ (P → Q)
  [↔]-one-direction with excluded-middle(P) | excluded-middle(Q)
  [↔]-one-direction | [∨]-introₗ p  | [∨]-introₗ q  = [∨]-introₗ (const p)
  [↔]-one-direction | [∨]-introₗ p  | [∨]-introᵣ nq = [∨]-introₗ (const p)
  [↔]-one-direction | [∨]-introᵣ np | [∨]-introₗ q  = [∨]-introᵣ (const q)
  [↔]-one-direction | [∨]-introᵣ np | [∨]-introᵣ nq = [∨]-introᵣ ([⊥]-elim ∘ np)

module _ {X : Type{ℓ₁}} ⦃ _ : ◊ X ⦄ {P : X → Stmt{ℓ₂}} ⦃ classical-expx : Classical(∃ P) ⦄ {Q : X → Stmt{ℓ₃}} where
  [∃][←]-distributivity : ∃(x ↦ (P(x) → Q(x))) ← (∃(x ↦ P(x)) → ∃(x ↦ Q(x)))
  [∃][←]-distributivity (expx-exqx) =
      (([∃]-map-proof (\{x} → proof ↦ proof{x})
        (([∃]-map-proof (\{x} → [↔]-to-[←] ([∀]-unrelatedₗ-[→] {X = X}{P}{Q(x)}))
          (([∃]-unrelatedᵣ-[→]ₗ ⦃ classical-expx ⦄
            (expx-exqx :of: (∃(x ↦ P(x)) → ∃(x ↦ Q(x))))
          )            :of: (∃(x ↦ (∃(x ↦ P(x)) → Q(x)))))
        )              :of: (∃(x ↦ ∀ₗ(y ↦ (P(y) → Q(x))))))
      )                :of: (∃(x ↦ (P(x) → Q(x)))))
    -- ∃(x ↦ P(x)) → ∃(x ↦ Q(x))
    -- ⇒ ∃(x ↦ ∃(x ↦ P(x)) → Q(x))
    -- ⇒ ∃(x ↦ ∀(y ↦ P(y) → Q(x)))
    -- ⇒ ∃(x ↦ P(x) → Q(x))

-- TODO: Maybe try to get rid of the second instance assumption? Idea: Only [¬¬]-elim is needed for that one, so if possible and true, prove: (∀{x} → Classic(P(x)) → P(x)) → (Classic(∃ P) → (∃ P)). No, that is probably not true
module _ {X : Type{ℓ₁}}{P : X → Stmt{ℓ₂}} ⦃ classical-proof1 : ∀{x} → Classical(P(x)) ⦄ ⦃ classical-proof2 : Classical(∃(¬_ ∘ P)) ⦄ where
  [¬∀]-to-[∃¬] : ∃(x ↦ ¬(P(x))) ← (¬ ∀ₗ(x ↦ P(x)))
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

Classical₁ : ∀{ℓₒ ℓₗ}{X : Type{ℓₒ}} → (X → Stmt{ℓₗ}) → Stmt{ℓₒ ⊔ ℓₗ}
Classical₁(P) = ∀¹(Classical ∘₁ P)
-- Classical₁(P) = ∀{x} → Classical(P(x))

Classical₂ : ∀{ℓₒ₁ ℓₒ₂ ℓₗ}{X : Type{ℓₒ₁}}{Y : Type{ℓₒ₂}} → (X → Y → Stmt{ℓₗ}) → Stmt{ℓₒ₁ ⊔ ℓₒ₂ ⊔ ℓₗ}
Classical₂(P) = ∀²(Classical ∘₂ P)
-- Classical₂(P) = ∀{x}{y} → Classical(P(x)(y))

Classical₃ : ∀{ℓₒ₁ ℓₒ₂ ℓₒ₃ ℓₗ}{X : Type{ℓₒ₁}}{Y : Type{ℓₒ₂}}{Z : Type{ℓₒ₃}} → (X → Y → Z → Stmt{ℓₗ}) → Stmt{ℓₒ₁ ⊔ ℓₒ₂ ⊔ ℓₒ₃ ⊔ ℓₗ}
Classical₃(P) = ∀³(Classical ∘₃ P)
-- Classical₃(P) = ∀{x}{y}{z} → Classical(P(x)(y)(z))
