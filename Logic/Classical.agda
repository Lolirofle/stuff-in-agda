module Logic.Classical{ℓ} where

open import Data.Either as Either using (_‖_)
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Logic.Propositional{ℓ}
open import Logic.Propositional.Theorems{ℓ}
open import Logic.Predicate{ℓ}{ℓ}
open import Logic.Predicate.Theorems{ℓ}{ℓ}
open import Type
open import Type.Empty

-- A proposition is behaving classically when excluded middle holds for it.
-- In other words: For the proposition or its negation, if one of them is provable.
-- It could be interpreted as: The proposition is either true or false.
-- In classical logic, this is always the case for any proposition.
-- Sometimes (∀x. Classical(P(x))) is called: P is decidable
record Classical (P : Stmt) : Stmt where
  instance constructor intro
  field
    ⦃ excluded-middle ⦄ : P ∨ (¬ P)

  -- Double negation elimination
  [¬¬]-elim : (¬¬ P) → P
  [¬¬]-elim = [¬¬]-elim-from-excluded-middle (excluded-middle)

  -- Contraposition rule in reverse
  contrapositiveₗ : ∀{Q : Stmt} → (Q → P) ← ((¬ Q) ← (¬ P))
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
  [→]-disjunctive-formᵣ : ∀{Q : Stmt} → (P → Q) → ((¬ P) ∨ Q)
  [→]-disjunctive-formᵣ (pq) with excluded-middle
  ... | [∨]-introₗ(p)  = [∨]-introᵣ(pq(p))
  ... | [∨]-introᵣ(np) = [∨]-introₗ(np)

  -- One direction of the equivalence of implication using conjunction
  [→][∧]ₗ : ∀{Q : Stmt} → (Q → P) ← ¬(Q ∧ (¬ P))
  [→][∧]ₗ (nqnp) = [¬¬]-elim ∘ (Tuple.curry(nqnp))
    -- ¬(A ∧ ¬B) → (A → ¬¬B)
    --   ¬(A ∧ (¬ B)) //assumption
    --   ((A ∧ (B → ⊥)) → ⊥) //Definition: (¬)
    --   (A → (B → ⊥) → ⊥) //Tuple.curry
    --   (A → ¬(B → ⊥)) //Definition: (¬)
    --   (A → ¬(¬ B)) //Definition: (¬)

  -- The type signature of the "call/cc or "call-with-current-continuation" subroutine in the programming language Scheme
  -- Also known as: "Peirce's law"
  call-cc : ∀{Q : Stmt} → (((P → Q) → P) → P)
  call-cc (pqp) with excluded-middle
  ... | ([∨]-introₗ p ) = p
  ... | ([∨]-introᵣ np) = pqp([⊥]-elim ∘ np)

  contrapositive-variantₗ : ∀{Q : Stmt} → ((¬ P) → Q) → (P ← (¬ Q))
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

  [∃]-unrelatedᵣ-[→]ₗ : ∀{X} → ⦃ _ : ◊ X ⦄ → ∀{Q : X → Stmt} → ∃(x ↦ (P → Q(x))) ← (P → ∃(x ↦ Q(x)))
  [∃]-unrelatedᵣ-[→]ₗ {X} ⦃ ◊.intro ⦃ x ⦄ ⦄ {Q} = l where
    l : ∃(x ↦ (P → Q(x))) ← (P → ∃(x ↦ Q(x)))
    l(pexqx) with excluded-middle
    ... | ([∨]-introₗ p)  = [∃]-map (const) (pexqx(p))
    ... | ([∨]-introᵣ np) = [∃]-intro(x) ⦃ ([⊥]-elim{Q(x)}) ∘ np ⦄

open Classical ⦃ ... ⦄ public

{- TODO: Seems impossible to get the y
instance
  [∧]-classical-elimₗ : ∀{X Y} → ⦃ _ : Classical(X ∧ Y) ⦄ → Classical(X)
  [∧]-classical-elimₗ {X}{Y} ⦃ classical-xy ⦄ = classical-intro (proof) where
    proof : X ∨ (¬ X)
    proof with excluded-middle ⦃ classical-xy ⦄
    ... | [∨]-introₗ(xy)  = [∨]-introₗ([∧]-elimₗ(xy))
    ... | [∨]-introᵣ(nxy) = [∨]-introᵣ(x ↦ nxy([∧]-intro(x)(y)))
-}

classical-by-equivalence : ∀{X Y} → (X ↔ Y) → (Classical(X) ↔ Classical(Y))
classical-by-equivalence {X}{Y} (xy) = [↔]-intro (cy ↦ Classical.intro ⦃ proofₗ(cy) ⦄) (cx ↦ Classical.intro ⦃ proofᵣ(cx) ⦄) where
  proofᵣ : Classical(X) → (Y ∨ (¬ Y))
  proofᵣ (classical-x) with excluded-middle ⦃ classical-x ⦄
  ... | [∨]-introₗ(x)  = [∨]-introₗ([↔]-elimᵣ xy x)
  ... | [∨]-introᵣ(nx) = [∨]-introᵣ(nx ∘ ([↔]-elimₗ xy))

  proofₗ : Classical(Y) → (X ∨ (¬ X))
  proofₗ (classical-y) with excluded-middle ⦃ classical-y ⦄
  ... | [∨]-introₗ(y)  = [∨]-introₗ([↔]-elimₗ xy y)
  ... | [∨]-introᵣ(ny) = [∨]-introᵣ(ny ∘ ([↔]-elimᵣ xy))

instance
  [∧]-classical-intro : ∀{X Y} → ⦃ _ : Classical(X) ⦄ → ⦃ _ : Classical(Y) ⦄ → Classical(X ∧ Y)
  [∧]-classical-intro {X}{Y} ⦃ classical-x ⦄ ⦃ classical-y ⦄ = Classical.intro ⦃ proof ⦄ where
    proof : (X ∧ Y) ∨ (¬ (X ∧ Y))
    proof with (excluded-middle ⦃ classical-x ⦄ , excluded-middle ⦃ classical-y ⦄)
    ... | ([∨]-introₗ(x)  , [∨]-introₗ(y))  = [∨]-introₗ([∧]-intro(x)(y))
    ... | ([∨]-introₗ(x)  , [∨]-introᵣ(ny)) = [∨]-introᵣ(xy ↦ ny([∧]-elimᵣ(xy)))
    ... | ([∨]-introᵣ(nx) , [∨]-introₗ(y))  = [∨]-introᵣ(xy ↦ nx([∧]-elimₗ(xy)))
    ... | ([∨]-introᵣ(nx) , [∨]-introᵣ(ny)) = [∨]-introᵣ(xy ↦ nx([∧]-elimₗ(xy)))

instance
  [¬]-classical-intro : ∀{X} → ⦃ _ : Classical(X) ⦄ → Classical(¬ X)
  [¬]-classical-intro {X} ⦃ classical-x ⦄ = Classical.intro ⦃ proof ⦄ where
    proof : (¬ X) ∨ (¬¬ X)
    proof = Either.swap(Either.mapLeft [¬¬]-intro (excluded-middle ⦃ classical-x ⦄))

instance
  [∨]-classical-intro : ∀{X Y} → ⦃ _ : Classical(X) ⦄ → ⦃ _ : Classical(Y) ⦄ → Classical(X ∨ Y)
  [∨]-classical-intro {X}{Y} ⦃ classical-x ⦄ ⦃ classical-y ⦄ = Classical.intro ⦃ proof ⦄ where
    proof : (X ∨ Y) ∨ (¬ (X ∨ Y))
    proof with (excluded-middle ⦃ classical-x ⦄ , excluded-middle ⦃ classical-y ⦄)
    ... | ([∨]-introₗ(x)  , [∨]-introₗ(y))  = [∨]-introₗ([∨]-introₗ(x))
    ... | ([∨]-introₗ(x)  , [∨]-introᵣ(ny)) = [∨]-introₗ([∨]-introₗ(x))
    ... | ([∨]-introᵣ(nx) , [∨]-introₗ(y))  = [∨]-introₗ([∨]-introᵣ(y))
    ... | ([∨]-introᵣ(nx) , [∨]-introᵣ(ny)) = [∨]-introᵣ(xy ↦ [∨]-elim(nx)(ny) (xy))

instance
  [→]-classical-intro : ∀{X Y} → ⦃ _ : Classical(X) ⦄ → ⦃ _ : Classical(Y) ⦄ → Classical(X → Y)
  [→]-classical-intro {X}{Y} ⦃ classical-x ⦄ ⦃ classical-y ⦄ = Classical.intro ⦃ proof ⦄ where
    proof : (X → Y) ∨ (¬ (X → Y))
    proof with (excluded-middle ⦃ classical-x ⦄ , excluded-middle ⦃ classical-y ⦄)
    ... | ([∨]-introₗ(x)  , [∨]-introₗ(y))  = [∨]-introₗ(const(y))
    ... | ([∨]-introₗ(x)  , [∨]-introᵣ(ny)) = [∨]-introᵣ([¬→][∧]ₗ ([∧]-intro x ny))
    ... | ([∨]-introᵣ(nx) , [∨]-introₗ(y))  = [∨]-introₗ(const(y))
    ... | ([∨]-introᵣ(nx) , [∨]-introᵣ(ny)) = [∨]-introₗ([⊥]-elim ∘ nx)

instance
  [↔]-classical-intro : ∀{X Y} → ⦃ _ : Classical(X) ⦄ → ⦃ _ : Classical(Y) ⦄ → Classical(X ↔ Y)
  [↔]-classical-intro {X}{Y} ⦃ classical-x ⦄ ⦃ classical-y ⦄ = Classical.intro ⦃ proof ⦄ where
    proof : (X ↔ Y) ∨ (¬ (X ↔ Y))
    proof with (excluded-middle ⦃ classical-x ⦄ , excluded-middle ⦃ classical-y ⦄)
    ... | ([∨]-introₗ(x)  , [∨]-introₗ(y))  = [∨]-introₗ([↔]-intro (const(x)) (const(y)))
    ... | ([∨]-introₗ(x)  , [∨]-introᵣ(ny)) = [∨]-introᵣ(([¬→][∧]ₗ ([∧]-intro x ny)) ∘ [↔]-elimᵣ)
    ... | ([∨]-introᵣ(nx) , [∨]-introₗ(y))  = [∨]-introᵣ(([¬→][∧]ₗ ([∧]-intro y nx)) ∘ [↔]-elimₗ)
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

instance
  [∃]-classical-elim : ∀{X} → ⦃ _ : ◊ X ⦄ → ∀{P : X → Stmt} → ⦃ _ : Classical(∃ P) ⦄ → ∃(x ↦ Classical(P(x)))
  [∃]-classical-elim {X}{P} ⦃ classical-expx ⦄ with excluded-middle ⦃ classical-expx ⦄
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

[¬][∧]ₗ : ∀{X Y : Stmt} → ⦃ _ : Classical(X) ⦄ → ⦃ _ : Classical(Y) ⦄ → ((¬ X) ∨ (¬ Y)) ← (¬ (X ∧ Y))
[¬][∧]ₗ {X}{Y} ⦃ classic-x ⦄ ⦃ classic-y ⦄ (nxy) =
  [→]-disjunctive-formᵣ {X} ⦃ classic-x ⦄ {¬ Y} ([→][∧]ₗ ⦃ [¬]-classical-intro ⦃ classic-y ⦄ ⦄ (nxy ∘ (Tuple.mapRight ([¬¬]-elim ⦃ classic-y ⦄))))
  -- ((X ∧ Y) → ⊥) → ((X → ⊥) ∨ (Y → ⊥))
  -- ¬((X ∧ Y) → ⊥) ← ¬((X → ⊥) ∨ (Y → ⊥))

-- TODO: Is this provable constructively? Doesn't seem like it?
[¬→][∧]ᵣ : ∀{X Y : Stmt} → ⦃ _ : Classical(X) ⦄ → ⦃ _ : Classical(Y) ⦄ → ¬(X → Y) → (X ∧ (¬ Y))
[¬→][∧]ᵣ ⦃ classic-x ⦄ ⦃ classic-y ⦄ = contrapositive-variantₗ ⦃ [∧]-classical-intro ⦃ classic-x ⦄ ⦃ [¬]-classical-intro ⦃ classic-y ⦄ ⦄ ⦄ ([→][∧]ₗ ⦃ classic-y ⦄)

[↔]-negationₗ : ∀{X Y} → ⦃ _ : Classical(X) ⦄ → ⦃ _ : Classical(Y) ⦄ → (X ↔ Y) ← ((¬ X) ↔ (¬ Y))
[↔]-negationₗ {X}{Y} ⦃ classic-x ⦄ ⦃ classic-y ⦄ ([↔]-intro nynx nxny) = [↔]-intro yx xy where
  yx : Y → X
  yx = contrapositiveₗ ⦃ classic-x ⦄ nxny

  xy : X → Y
  xy = contrapositiveₗ ⦃ classic-y ⦄ nynx

[∃][←]-distributivity : ∀{X} → ⦃ _ : ◊ X ⦄ → ∀{P : X → Stmt} → ⦃ _ : Classical(∃ P) ⦄ → ∀{Q : X → Stmt} → ∃(x ↦ (P(x) → Q(x))) ← (∃(x ↦ P(x)) → ∃(x ↦ Q(x)))
[∃][←]-distributivity {X}{P} ⦃ classical-expx ⦄ {Q} (expx-exqx) =
    (([∃]-map (\{x} → proof ↦ proof{x})
      (([∃]-map (\{x} → [↔]-elimₗ ([∀]-unrelatedₗ-[→] {X}{P}{Q(x)}))
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
module _ {X}{P : X → Stmt} ⦃ classical-proof1 : ∀{x} → Classical(P(x)) ⦄ ⦃ classical-proof2 : Classical(∃(¬_ ∘ P)) ⦄ where
  [¬∀]-to-[∃¬] : ∃(x ↦ ¬(P(x))) ← (¬ ∀ₗ(x ↦ P(x)))
  [¬∀]-to-[∃¬] (naxpx) =
    ([¬¬]-elim ⦃ classical-proof2 ⦄
      ([¬]-intro {¬ ∃(x ↦ ¬(P(x)))} (nexnpx ↦
        (naxpx
          ([∀][→]-distributivity {X}{¬¬_ ∘ P}
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
  ... | ([∨]-introᵣ naxpx) = [∃]-map ([⊥]-elim ∘_) ([¬∀]-to-[∃¬] (naxpx))

  drinker-ambiguity-equiv : ⦃ _ : Classical(∀ₗ P) ⦄ → ((◊ X) ↔ ∃(x ↦ (P(x) → ∀{y} → P(y))))
  drinker-ambiguity-equiv ⦃ classical-axpx ⦄ =
    [↔]-intro
      (\ex → ◊.intro ⦃ [∃]-witness ex ⦄)
      (\pos-x → drinker-ambiguity ⦃ pos-x ⦄ ⦃ classical-axpx ⦄)

  -- TODO: Why is this proof so similar to the proof of `drinker-ambiguity`? Seems like that one is a special case of this when Q is (∀ₗ P) here
  [∃]-unrelatedₗ-[→]ₗ : ⦃ _ : ◊ X ⦄ → ⦃ _ : Classical(∀ₗ P) ⦄ → ∀{Q : Stmt} → ∃(x ↦ (P(x) → Q)) ← (∀ₗ(x ↦ P(x)) → Q)
  [∃]-unrelatedₗ-[→]ₗ ⦃ pos-x ⦄ ⦃ classical-axpx ⦄ {Q} = l where
    l : ∃(x ↦ (P(x) → Q)) ← (∀ₗ(x ↦ P(x)) → Q)
    l(axpxq) with excluded-middle ⦃ classical-axpx ⦄
    ... | ([∨]-introₗ axpx)  = [∃]-intro([◊]-existence) ⦃ const(axpxq (axpx)) ⦄
    ... | ([∨]-introᵣ naxpx) = [∃]-map ([⊥]-elim ∘_) ([¬∀]-to-[∃¬] (naxpx))
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
