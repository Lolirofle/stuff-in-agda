module Logic.Classical where

open import Data.Either as Either using (_‖_)
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Logic.Predicate
open import Logic.Predicate.Theorems
open import Type
open import Type.Empty

-- A proposition is behaving classically when excluded middle holds for it.
-- In other words: For the proposition or its negation, if one of them is provable.
-- It could be interpreted as: The proposition is either true or false.
-- In classical logic, this is always the case for any proposition.
-- Sometimes (∀x. Classical(P(x))) is called: P is decidable
record Classical {ℓ} (P : Stmt{ℓ}) : Stmt{ℓ} where
  constructor intro
  field
    ⦃ excluded-middle ⦄ : P ∨ (¬ P)

  -- Double negation elimination
  [¬¬]-elim : (¬¬ P) → P
  [¬¬]-elim = [¬¬]-elim-from-excluded-middle (excluded-middle)

  module _ {ℓ₂} where
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
    contrapositive-variantₗ {Q} npq nq = nqnp(nq) where
      npnnq : (¬ P) → (¬¬ Q)
      npnnq = [¬¬]-intro ∘ npq

      nqnp : (¬ Q) → P
      nqnp = contrapositiveₗ (npnnq)

    -- Also known as: "Clavius's Law"
    negative-implies-positive : ((¬ P) → P) → P
    negative-implies-positive npp with excluded-middle
    ... | ([∨]-introₗ p ) = p
    ... | ([∨]-introᵣ np) = npp np

  module _ {ℓ₂ ℓ₃} where
    [∃]-unrelatedᵣ-[→]ₗ : ∀{X : Type{ℓ₂}} → ⦃ _ : ◊ X ⦄ → ∀{Q : X → Stmt{ℓ₃}} → ∃(x ↦ (P → Q(x))) ← (P → ∃(x ↦ Q(x)))
    [∃]-unrelatedᵣ-[→]ₗ {X} ⦃ ◊.intro ⦃ x ⦄ ⦄ {Q} = l where
      l : ∃(x ↦ (P → Q(x))) ← (P → ∃(x ↦ Q(x)))
      l(pexqx) with excluded-middle
      ... | ([∨]-introₗ p)  = [∃]-map-proof (const) (pexqx(p))
      ... | ([∨]-introᵣ np) = [∃]-intro(x) ⦃ ([⊥]-elim{P = Q(x)}) ∘ np ⦄

open Classical ⦃ ... ⦄ public

module _ {ℓ} {P : Stmt{ℓ}} where
  instance
    [¬]-classical-intro : ⦃ _ : Classical(P) ⦄ → Classical(¬ P)
    [¬]-classical-intro ⦃ classical-p ⦄ = Classical.intro ⦃ proof ⦄ where
      proof : (¬ P) ∨ (¬¬ P)
      proof = Either.swap(Either.mapLeft [¬¬]-intro (excluded-middle ⦃ classical-p ⦄))

module _ {ℓ₁ ℓ₂} {P : Stmt{ℓ₁}} {Q : Stmt{ℓ₂}} where
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
  classical-by-equivalence (xy) = [↔]-intro (cy ↦ Classical.intro ⦃ proofₗ(cy) ⦄) (cx ↦ Classical.intro ⦃ proofᵣ(cx) ⦄) where
    proofᵣ : Classical(P) → (Q ∨ (¬ Q))
    proofᵣ (classical-p) with excluded-middle ⦃ classical-p ⦄
    ... | [∨]-introₗ(p)  = [∨]-introₗ([↔]-to-[→] xy p)
    ... | [∨]-introᵣ(nx) = [∨]-introᵣ(nx ∘ ([↔]-to-[←] xy))

    proofₗ : Classical(Q) → (P ∨ (¬ P))
    proofₗ (classical-q) with excluded-middle ⦃ classical-q ⦄
    ... | [∨]-introₗ(q)  = [∨]-introₗ([↔]-to-[←] xy q)
    ... | [∨]-introᵣ(ny) = [∨]-introᵣ(ny ∘ ([↔]-to-[→] xy))

  instance
    [∧]-classical-intro : ⦃ _ : Classical(P) ⦄ → ⦃ _ : Classical(Q) ⦄ → Classical(P ∧ Q)
    [∧]-classical-intro ⦃ classical-p ⦄ ⦃ classical-q ⦄ = Classical.intro ⦃ proof ⦄ where
      proof : (P ∧ Q) ∨ (¬ (P ∧ Q))
      proof with (excluded-middle ⦃ classical-p ⦄ , excluded-middle ⦃ classical-q ⦄)
      ... | ([∨]-introₗ(p)  , [∨]-introₗ(q))  = [∨]-introₗ([∧]-intro(p)(q))
      ... | ([∨]-introₗ(p)  , [∨]-introᵣ(ny)) = [∨]-introᵣ(xy ↦ ny([∧]-elimᵣ(xy)))
      ... | ([∨]-introᵣ(nx) , [∨]-introₗ(q))  = [∨]-introᵣ(xy ↦ nx([∧]-elimₗ(xy)))
      ... | ([∨]-introᵣ(nx) , [∨]-introᵣ(ny)) = [∨]-introᵣ(xy ↦ nx([∧]-elimₗ(xy)))

  instance
    [∨]-classical-intro : ⦃ _ : Classical(P) ⦄ → ⦃ _ : Classical(Q) ⦄ → Classical(P ∨ Q)
    [∨]-classical-intro ⦃ classical-p ⦄ ⦃ classical-q ⦄ = Classical.intro ⦃ proof ⦄ where
      proof : (P ∨ Q) ∨ (¬ (P ∨ Q))
      proof with (excluded-middle ⦃ classical-p ⦄ , excluded-middle ⦃ classical-q ⦄)
      ... | ([∨]-introₗ(p)  , [∨]-introₗ(q))  = [∨]-introₗ([∨]-introₗ(p))
      ... | ([∨]-introₗ(p)  , [∨]-introᵣ(ny)) = [∨]-introₗ([∨]-introₗ(p))
      ... | ([∨]-introᵣ(nx) , [∨]-introₗ(q))  = [∨]-introₗ([∨]-introᵣ(q))
      ... | ([∨]-introᵣ(nx) , [∨]-introᵣ(ny)) = [∨]-introᵣ(xy ↦ [∨]-elim(nx)(ny) (xy))

  instance
    [→]-classical-intro : ⦃ _ : Classical(P) ⦄ → ⦃ _ : Classical(Q) ⦄ → Classical(P → Q)
    [→]-classical-intro ⦃ classical-p ⦄ ⦃ classical-q ⦄ = Classical.intro ⦃ proof ⦄ where
      proof : (P → Q) ∨ (¬ (P → Q))
      proof with (excluded-middle ⦃ classical-p ⦄ , excluded-middle ⦃ classical-q ⦄)
      ... | ([∨]-introₗ(p)  , [∨]-introₗ(q))  = [∨]-introₗ(const(q))
      ... | ([∨]-introₗ(p)  , [∨]-introᵣ(ny)) = [∨]-introᵣ([¬→][∧]ₗ ([∧]-intro p ny))
      ... | ([∨]-introᵣ(nx) , [∨]-introₗ(q))  = [∨]-introₗ(const(q))
      ... | ([∨]-introᵣ(nx) , [∨]-introᵣ(ny)) = [∨]-introₗ([⊥]-elim ∘ nx)

  instance
    [↔]-classical-intro : ⦃ _ : Classical(P) ⦄ → ⦃ _ : Classical(Q) ⦄ → Classical(P ↔ Q)
    [↔]-classical-intro ⦃ classical-p ⦄ ⦃ classical-q ⦄ = Classical.intro ⦃ proof ⦄ where
      proof : (P ↔ Q) ∨ (¬ (P ↔ Q))
      proof with (excluded-middle ⦃ classical-p ⦄ , excluded-middle ⦃ classical-q ⦄)
      ... | ([∨]-introₗ(p)  , [∨]-introₗ(q))  = [∨]-introₗ([↔]-intro (const(p)) (const(q)))
      ... | ([∨]-introₗ(p)  , [∨]-introᵣ(ny)) = [∨]-introᵣ(([¬→][∧]ₗ ([∧]-intro p ny)) ∘ [↔]-to-[→])
      ... | ([∨]-introᵣ(nx) , [∨]-introₗ(q))  = [∨]-introᵣ(([¬→][∧]ₗ ([∧]-intro q nx)) ∘ [↔]-to-[←])
      ... | ([∨]-introᵣ(nx) , [∨]-introᵣ(ny)) = [∨]-introₗ([↔]-intro ([⊥]-elim ∘ ny) ([⊥]-elim ∘ nx))

instance
  [⊤]-classical-intro : Classical(⊤)
  [⊤]-classical-intro = Classical.intro ⦃ proof ⦄ where
    proof : ⊤ ∨ (¬ ⊤)
    proof = [∨]-introₗ ([⊤]-intro)

instance
  [⊥]-classical-intro : Classical(⊥)
  [⊥]-classical-intro = Classical.intro ⦃ proof ⦄ where
    proof : ⊥ ∨ (¬ ⊥)
    proof = [∨]-introᵣ (id)

module _ {ℓ₁ ℓ₂} {X : Type{ℓ₁}} ⦃ _ : (◊ X) ⦄ {P : X → Stmt{ℓ₂}} where
  instance
    [∃]-classical-elim : ⦃ _ : Classical(∃ P) ⦄ → ∃(x ↦ Classical(P(x)))
    [∃]-classical-elim ⦃ classical-expx ⦄ with excluded-middle ⦃ classical-expx ⦄
    ... | [∨]-introₗ(expx)  = [∃]-intro([∃]-witness(expx)) ⦃ Classical.intro ⦃ [∨]-introₗ([∃]-proof(expx)) ⦄ ⦄
    ... | [∨]-introᵣ(nexpx) = [∃]-intro([◊]-existence) ⦃ Classical.intro ⦃ [∨]-introᵣ(axnpx{[◊]-existence}) ⦄ ⦄ where
      axnpx = [¬∃]-to-[∀¬] (nexpx)

-- TODO: Here I tried to prove some stuff that probably are unprovable. Also, see https://ncatlab.org/nlab/show/principle+of+omniscience . That thing cannot be proven

-- instance
--   [∀][∃]-classical-elim : ∀{X} → ⦃ _ : ◊ X ⦄ → ∀{P : X → Stmt} → ⦃ _ : Classical(∀ₗ P) ⦄ → ⦃ _ : Classical(∃ P) ⦄ → ∀{x} → Classical(P(x))
--   [∀][∃]-classical-elim {X}{P} ⦃ classical-axpx ⦄ ⦃ classical-expx ⦄ {x} = Classical.intro ⦃ proof ⦄ where
--     proof : P(x) ∨ (¬ P(x))
--     proof with (excluded-middle ⦃ classical-axpx ⦄ , excluded-middle ⦃ classical-expx ⦄)
--     ... | ([∨]-introₗ(axpx)  , [∨]-introₗ(expx))  = [∨]-introₗ(axpx{x})
--     ... | ([∨]-introₗ(axpx)  , [∨]-introₗ(nexpx)) = [∨]-introᵣ(axpx{x})
--     ... | ([∨]-introᵣ(naxpx) , [∨]-introₗ(expx))  = [∨]-introᵣ(?)
--     ... | ([∨]-introᵣ(naxpx) , [∨]-introᵣ(nexpx)) = [∨]-introₗ([¬∃]-to-[∀¬] nexpx {x})

-- instance
--   [∃¬]-classical-intro : ∀{X} → ⦃ _ : ◊ X ⦄ → ∀{P : X → Stmt} → ⦃ _ : ∀{x} → Classical(P(x)) ⦄ → ⦃ _ : Classical(∃ P) ⦄ → Classical(∃(¬_ ∘ P))
--   [∃¬]-classical-intro {X}{P} ⦃ classical-p ⦄ ⦃ classical-expx ⦄ = Classical.intro ⦃ proof ⦄ where
--     proof : ∃(¬_ ∘ P) ∨ ¬(∃(¬_ ∘ P))
--     proof with excluded-middle ⦃ classical-expx ⦄
--     ... | [∨]-introₗ(expx)  = [∨]-introᵣ(axnpx{[◊]-existence})
--     ... | [∨]-introᵣ(nexpx) = [∨]-introₗ([¬¬]-elim([¬∃]-to-[∀¬] ∘ naxnpx))

-- instance
--   [∃¬]-classical-elim : ∀{X}{P} → ⦃ _ : Classical(∀ₗ P) ⦄ → ⦃ _ : Classical(∃ P) ⦄ → Classical(∃(¬_ ∘ P))
--   [∃¬]-classical-elim {X}{P} ⦃ classical-axpx ⦄ ⦃ classical-expx ⦄ {x} = Classical.intro ⦃ proof ⦄ where
--     proof : ∃(¬_ ∘ P) ∨ ¬(∃(¬_ ∘ P))
--     proof with excluded-middle ⦃ classical-axpx ⦄ | excluded-middle ⦃ classical-expx ⦄
--     ... | [∨]-introₗ(axpx)  | [∨]-introₗ(expx)  = [∨]-introₗ(axpx{x})
--     ... | [∨]-introₗ(axpx)  | [∨]-introᵣ(nexpx) = [∨]-introₗ(axpx{x})
--     ... | [∨]-introᵣ(naxpx) | [∨]-introₗ(expx)  = [∨]-introᵣ(axnpx{x})
--     ... | [∨]-introᵣ(naxpx) | [∨]-introᵣ(nexpx) = [∨]-introᵣ(naxpx)

-- instance
--   [∀]-classical-elim : ∀{X}{P} → ⦃ _ : Classical(∀ₗ P) ⦄ → ⦃ _ : Classical(∃ P) ⦄ → ∀{x} → Classical(P(x))
--   [∀]-classical-elim {X}{P} ⦃ classical-axpx ⦄ ⦃ classical-expx ⦄ {x} = Classical.intro ⦃ proof ⦄ where
--     proof : P(x) ∨ ¬(P(x))
--     proof with excluded-middle ⦃ classical-axpx ⦄ | excluded-middle ⦃ classical-expx ⦄
--     ... | [∨]-introₗ(axpx)  | [∨]-introₗ(expx)  = [∨]-introₗ(axpx{x})
--     ... | [∨]-introₗ(axpx)  | [∨]-introᵣ(nexpx) = [∨]-introₗ(axpx{x})
--     ... | [∨]-introᵣ(naxpx) | [∨]-introₗ(expx)  = [∨]-introᵣ(axnpx{x})
--     ... | [∨]-introᵣ(naxpx) | [∨]-introᵣ(nexpx) = [∨]-introᵣ(naxpx)

-- instance
--   [∃]-classical-elim : ∀{X}{P} → ⦃ _ : Classical(∃ₗ P) ⦄ → ∀{x} → Classical(P(x))
--   [∃]-classical-elim {X}{P} ⦃ classical-expx ⦄ {x} = Classical.intro ⦃ proof ⦄ where
--     proof : P(x) ∨ (¬ P(x))
--     proof with excluded-middle ⦃ classical-axpx ⦄
--     ... | [∨]-introₗ(expx)  = [∨]-introₗ(expx{x})
--     ... | [∨]-introᵣ(eaxpx) = [∨]-introᵣ(expx ↦ ∃)

module _ {ℓ₁ ℓ₂} {P : Stmt{ℓ₁}} {Q : Stmt{ℓ₂}} where
  [¬][∧]ₗ : ⦃ _ : Classical(P) ⦄ → ⦃ _ : Classical(Q) ⦄ → ((¬ P) ∨ (¬ Q)) ← (¬ (P ∧ Q))
  [¬][∧]ₗ ⦃ classic-p ⦄ ⦃ classic-q ⦄ (npq) =
    [→]-disjunctive-formᵣ {P = P} ⦃ classic-p ⦄ {Q = ¬ Q} ([→][∧]ₗ ⦃ [¬]-classical-intro ⦃ classic-q ⦄ ⦄ (npq ∘ (Tuple.mapRight ([¬¬]-elim ⦃ classic-q ⦄))))
    -- ((P ∧ Q) → ⊥) → ((P → ⊥) ∨ (Q → ⊥))
    -- ¬((P ∧ Q) → ⊥) ← ¬((P → ⊥) ∨ (Q → ⊥))

  -- TODO: Is this provable constructivelq? Doesn't seem like it?
  [¬→][∧]ᵣ : ⦃ _ : Classical(P) ⦄ → ⦃ _ : Classical(Q) ⦄ → ¬(P → Q) → (P ∧ (¬ Q))
  [¬→][∧]ᵣ ⦃ classic-p ⦄ ⦃ classic-q ⦄ = contrapositive-variantₗ ⦃ [∧]-classical-intro ⦃ classic-p ⦄ ⦃ [¬]-classical-intro ⦃ classic-q ⦄ ⦄ ⦄ ([→][∧]ₗ ⦃ classic-q ⦄)

  [↔]-negationₗ : ⦃ _ : Classical(P) ⦄ → ⦃ _ : Classical(Q) ⦄ → (P ↔ Q) ← ((¬ P) ↔ (¬ Q))
  [↔]-negationₗ ⦃ classic-p ⦄ ⦃ classic-q ⦄ ([↔]-intro nqnp npnq) = [↔]-intro qp pq where
    qp : Q → P
    qp = contrapositiveₗ ⦃ classic-p ⦄ npnq

    pq : P → Q
    pq = contrapositiveₗ ⦃ classic-q ⦄ nqnp

module _ {ℓ₁ ℓ₂ ℓ₃} {X : Type{ℓ₁}} ⦃ _ : ◊ X ⦄ {P : X → Stmt{ℓ₂}} ⦃ classical-expx : Classical(∃ P) ⦄ {Q : X → Stmt{ℓ₃}} where
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
module _ {ℓ₁ ℓ₂} {X : Type{ℓ₁}}{P : X → Stmt{ℓ₂}} ⦃ classical-proof1 : ∀{x} → Classical(P(x)) ⦄ ⦃ classical-proof2 : Classical(∃(¬_ ∘ P)) ⦄ where
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

  -- Also known as: Drinker paradox
  drinker-ambiguity : ⦃ _ : ◊ X ⦄ → ⦃ _ : Classical(∀ₗ P) ⦄ → ∃(x ↦ (P(x) → ∀{y} → P(y)))
  drinker-ambiguity ⦃ pos-x ⦄ ⦃ classical-axpx ⦄ with excluded-middle ⦃ classical-axpx ⦄
  ... | ([∨]-introₗ axpx)  = [∃]-intro ([◊]-existence ⦃ pos-x ⦄) ⦃ const(\{x} → axpx{x}) ⦄
  ... | ([∨]-introᵣ naxpx) = [∃]-map-proof ([⊥]-elim ∘_) ([¬∀]-to-[∃¬] (naxpx))

  drinker-ambiguity-equiv : ⦃ _ : Classical(∀ₗ P) ⦄ → ((◊ X) ↔ ∃(x ↦ (P(x) → ∀{y} → P(y))))
  drinker-ambiguity-equiv ⦃ classical-axpx ⦄ =
    [↔]-intro
      (\ex → ◊.intro ⦃ [∃]-witness ex ⦄)
      (\pos-x → drinker-ambiguity ⦃ pos-x ⦄ ⦃ classical-axpx ⦄)

module _ {ℓ₁ ℓ₂ ℓ₃} {X : Type{ℓ₁}}{P : X → Stmt{ℓ₂}} ⦃ classical-proof1 : ∀{x} → Classical(P(x)) ⦄ ⦃ classical-proof2 : Classical(∃(¬_ ∘ P)) ⦄ where
  -- TODO: Why is this proof so similar to the proof of `drinker-ambiguity`? Seems like that one is a special case of this when Q is (∀ₗ P) here
  [∃]-unrelatedₗ-[→]ₗ : ⦃ _ : ◊ X ⦄ → ⦃ _ : Classical(∀ₗ P) ⦄ → ∀{Q : Stmt{ℓ₃}} → ∃(x ↦ (P(x) → Q)) ← (∀ₗ(x ↦ P(x)) → Q)
  [∃]-unrelatedₗ-[→]ₗ ⦃ pos-x ⦄ ⦃ classical-axpx ⦄ {Q} = l where
    l : ∃(x ↦ (P(x) → Q)) ← (∀ₗ(x ↦ P(x)) → Q)
    l(axpxq) with excluded-middle ⦃ classical-axpx ⦄
    ... | ([∨]-introₗ axpx)  = [∃]-intro([◊]-existence) ⦃ const(axpxq (axpx)) ⦄
    ... | ([∨]-introᵣ naxpx) = [∃]-map-proof ([⊥]-elim ∘_) ([¬∀]-to-[∃¬] ⦃ classical-proof1 ⦄ ⦃ classical-proof2 ⦄ (naxpx))
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
