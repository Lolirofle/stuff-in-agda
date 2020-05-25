module Logic.Predicate.Theorems where

import      Lvl
open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Logic.Predicate
open import Syntax.Type
open import Type
open import Type.Empty using (◊ ; [◊]-existence)

------------------------------------------
-- Swapping nested quantifiers

module _ {ℓₒ₁}{ℓₒ₂}{ℓₗ} {X : Type{ℓₒ₁}}{Y : Type{ℓₒ₂}}{P : X → Y → Stmt{ℓₗ}} where
  [∀]-swap : ∀ₗ(x ↦ ∀ₗ(y ↦ P(x)(y))) → ∀ₗ(y ↦ ∀ₗ(x ↦ P(x)(y)))
  [∀]-swap(xypxy){y}{x} = xypxy{x}{y}

  [∃]-swap : ∃(x ↦ ∃(y ↦ P(x)(y))) → ∃(y ↦ ∃(x ↦ P(x)(y)))
  [∃]-swap([∃]-intro(x) ⦃ [∃]-intro(y) ⦃ proof ⦄ ⦄) = [∃]-intro(y) ⦃ [∃]-intro(x) ⦃ proof ⦄ ⦄

------------------------------------------
-- Introducing and eliminating unnecessary quantifiers when the predicate is constant

module _ {ℓₒ}{ℓₗ} {X : Type{ℓₒ}} ⦃ pos : ◊ X ⦄ {P : Stmt{ℓₗ}} where
  [∃]-unnecessary-intro : P → ∃{Obj = X}(x ↦ P)
  [∃]-unnecessary-intro(p) = [∃]-intro([◊]-existence ⦃ pos ⦄) ⦃ p ⦄

module _ {ℓₒ}{ℓₗ} {X : Type{ℓₒ}} {P : Stmt{ℓₗ}} where
  [∀]-unnecessary-intro : P → ∀ₗ{Obj = X}(x ↦ P)
  [∀]-unnecessary-intro(p){x} = p

  [∃]-unnecessary-elim : ∃{Obj = X}(x ↦ P) → P
  [∃]-unnecessary-elim([∃]-intro(_) ⦃ proof ⦄) = proof

module _ {ℓₒ}{ℓₗ} {X : Type{ℓₒ}} ⦃ pos : ◊ X ⦄ {P : Stmt{ℓₗ}} where
  -- Note:
  --   The following is unprovable:
  --   [∀]-unnecessary : ∀{X}{P : Stmt} → ∀ₗ{X}(x ↦ P) → P
  --   X is not guaranteed to not be the empty type, and even if it was, the ∀ function requires a constructed value. It seems to need a non-empty domain to quantify over.
  [∀ₑ]-unnecessary-elim : ∀ₗ{Obj = X}(x ↦ P) → P
  [∀ₑ]-unnecessary-elim = [∀ₑ]-elim{Obj = X} ⦃ pos ⦄

------------------------------------------
-- When quantifiers contradict

module _ {ℓₒ}{ℓₗ} {X : Type{ℓₒ}} {P : X → Stmt{ℓₗ}} where
  [∀][∃¬]-contradiction : ∀ₗ(x ↦ P(x)) → ∃(x ↦ ¬(P(x))) → ⊥
  [∀][∃¬]-contradiction(ap)(enp) =
    ([∃]-elim(\{a} → np ↦ (
      ([⊥]-intro
        ([∀]-elim{Obj = X}{P} ap(a))
        np
      )
    )) (enp))

  [∀¬][∃]-contradiction : ∀ₗ(x ↦ ¬ P(x)) → ∃(x ↦ P(x)) → ⊥
  [∀¬][∃]-contradiction (axnpx) (expx) =
    axnpx {[∃]-witness(expx)} ([∃]-proof(expx))

------------------------------------------
-- Moving in and out negation from quantifiers

module _ {ℓₒ}{ℓₗ} {X : Type{ℓₒ}} {P : X → Stmt{ℓₗ}} where
  [∃¬]-to-[¬∀] : (∃(x ↦ ¬(P(x)))) → ¬(∀ₗ(x ↦ P(x)))
  [∃¬]-to-[¬∀] = swap ([∀][∃¬]-contradiction {ℓₒ}{ℓₗ})

  [∀¬]-to-[¬∃] : ∀ₗ(x ↦ ¬(P(x))) → ¬(∃(x ↦ P(x)))
  [∀¬]-to-[¬∃] = [∀¬][∃]-contradiction {ℓₒ}{ℓₗ} {X}{P}
    -- [∀¬]-to-[¬∃] (anpx) =
    --   ([¬]-intro(epx ↦
    --     [∃]-elim(\{a} → pa ↦
    --       ([⊥]-intro
    --         pa
    --         (anpx{a})
    --       )
    --     )(epx)
    --   ))

  [¬∃]-to-[∀¬] : ∀ₗ(x ↦ ¬(P(x))) ← ¬(∃(x ↦ P(x)))
  [¬∃]-to-[∀¬] (nepx) =
    ([∀]-intro(a ↦
      (([¬]-intro(pa ↦
        (([⊥]-intro
          (([∃]-intro a ⦃ pa ⦄) :of: (∃(x ↦ P(x))))
          (nepx :of: ¬(∃(x ↦ P(x))))
        ) :of: ⊥)
      )) :of: ¬(P(a)))
    ))

module _ {ℓₒ}{ℓₗ} {X : Type{ℓₒ}} ⦃ pos : ◊ X ⦄ {P : X → Stmt{ℓₗ}} where
  [¬∃]-to-[∃¬] : ¬(∃ P) → ∃(¬_ ∘ P)
  [¬∃]-to-[∃¬] (nexpx) = [∃]-intro ([◊]-existence ⦃ pos ⦄) ⦃ [¬∃]-to-[∀¬] {ℓₒ}{ℓₗ} {X}{P} (nexpx) ⦄

  [¬∃]-to-[¬∀] : ¬(∃ P) → ¬(∀ₗ P)
  [¬∃]-to-[¬∀] = ([∃¬]-to-[¬∀] {ℓₒ}{ℓₗ} {X}{P}) ∘ [¬∃]-to-[∃¬]

  [∀¬]-to-[¬∀] : ∀ₗ(¬_ ∘ P) → ¬(∀ₗ P)
  [∀¬]-to-[¬∀] axnpx axpx = (axnpx{[◊]-existence ⦃ pos ⦄}) (axpx{[◊]-existence ⦃ pos ⦄})

------------------------------------------
-- Introducing negations to change quantifier

module _ {ℓₒ}{ℓₗ} {X : Type{ℓₒ}} {P : X → Stmt{ℓₗ}} where
  [∀]-to-[¬∃¬] : ∀ₗ(x ↦ P(x)) → (¬ ∃(x ↦ ¬(P(x))))
  [∀]-to-[¬∃¬] = [∀][∃¬]-contradiction {ℓₒ}{ℓₗ} {X}{P} -- [∃]-elim(\{a} → npa ↦ npa(p{a}))(ep)

  [∃]-to-[¬∀¬] : ∃(x ↦ P(x)) → (¬ ∀ₗ(x ↦ ¬(P(x))))
  [∃]-to-[¬∀¬] = swap ([∀¬][∃]-contradiction {ℓₒ}{ℓₗ} {X}{P})

------------------------------------------
-- Stuff using double negation

module _ {ℓₒ}{ℓₗ} {X : Type{ℓₒ}} {P : X → Stmt{ℓₗ}} where
  [∀¬¬][∃¬]-contradiction : ∀ₗ(x ↦ ¬¬(P(x))) → (∃(x ↦ ¬(P(x)))) → ⊥
  [∀¬¬][∃¬]-contradiction (annp)([∃]-intro(a) ⦃ na ⦄) =
    [∀][∃¬]-contradiction {ℓₒ}{ℓₗ} {X}{¬¬_ ∘ P} (annp)([∃]-intro(a) ⦃ [¬¬]-intro(na) ⦄)

  [∀¬¬]-to-[¬∃¬] : ∀ₗ(x ↦ ¬¬(P(x))) → (¬ ∃(x ↦ ¬(P(x))))
  [∀¬¬]-to-[¬∃¬] = [∀¬¬][∃¬]-contradiction

  [¬¬∀]-to-[¬∃¬] : ¬¬ ∀ₗ(x ↦ (P(x))) → (¬ ∃(x ↦ ¬(P(x))))
  [¬¬∀]-to-[¬∃¬] = contrapositiveᵣ ([∃¬]-to-[¬∀] {ℓₒ}{ℓₗ} {X}{P})
  -- [¬¬∀]-to-[¬∃¬] (annx) (enx) =
  --   ([⊥]-intro
  --     ([∃¬]-to-[¬∀](enx))
  --     (annx)
  --   )

  [¬∃¬]-to-[∀¬¬] : ¬(∃(x ↦ ¬(P(x)))) → ∀ₗ(x ↦ ¬¬(P(x)))
  [¬∃¬]-to-[∀¬¬] (nenx) {a} (npa) = nenx([∃]-intro(a) ⦃ npa ⦄)

  [¬¬∀]-to-[∀¬¬] : ¬¬ ∀ₗ(x ↦ (P(x))) → ∀ₗ(x ↦ ¬¬(P(x)))
  [¬¬∀]-to-[∀¬¬] = [¬∃¬]-to-[∀¬¬] ∘ [¬¬∀]-to-[¬∃¬]

  [∀]-to-[∃]-conditional-by-existence : ∃(P) → ∀{Q : X → Stmt{ℓₗ}} → ∀ₗ(x ↦ (P(x) → Q(x))) → ∃(x ↦ (P(x) ∧ Q(x)))
  ∃.witness ([∀]-to-[∃]-conditional-by-existence p pq) = [∃]-witness p
  ∃.proof   ([∀]-to-[∃]-conditional-by-existence p pq) = [∧]-intro ([∃]-proof p) (pq{[∃]-witness p} ([∃]-proof p))

  -- TODO: Probably unprovable because people said so. Not sure why. Maybe because (¬¬A is valid in constructive logic) ⇔ (A is valid in classical logic), and therefore this would not be possible because everything here is in constructive logic.
  -- [∀¬¬]-to-[¬¬∀] : ∀{X}{P : X → Stmt} → ¬¬∀ₗ(x ↦ (P(x))) ← ∀ₗ(x ↦ ¬¬(P(x)))

------------------------------------------
-- Changing quantifier

module _ {ℓₒ}{ℓₗ} {X : Type{ℓₒ}} ⦃ pos : ◊ X ⦄ {P : X → Stmt{ℓₗ}} where
  -- Note: If X would be empty, then this would be unprovable because [∀]-elim needs a constructed element.
  [∀ₑ]-to-[∃] : ∀ₗ(x ↦ P(x)) → ∃(x ↦ P(x))
  [∀ₑ]-to-[∃] (apx) =
    [∃]-intro ([◊]-existence ⦃ pos ⦄) ⦃ [∀ₑ]-elim{Obj = X}{P}(apx) ⦄

------------------------------------------
-- "Distributing" quantifiers into logical operators

module _ {ℓₒ}{ℓₗ₁}{ℓₗ₂} {X : Type{ℓₒ}}{P : X → Stmt{ℓₗ₁}}{Q : X → Stmt{ℓₗ₂}} where
  [∀][→]-distributivity : ∀ₗ(x ↦ (P(x) → Q(x))) → ∀ₗ(x ↦ P(x)) → ∀ₗ(x ↦ Q(x))
  [∀][→]-distributivity (PxQx) (Px) = PxQx(Px)

  [∀][∧]-distributivity : ∀ₗ(x ↦ (P(x) ∧ Q(x))) ↔ (∀ₗ(x ↦ P(x)) ∧ ∀ₗ(x ↦ Q(x)))
  [∀][∧]-distributivity = [↔]-intro l r where
    l : (∀ₗ(x ↦ P(x)) ∧ ∀ₗ(x ↦ Q(x))) → ∀ₗ(x ↦ (P(x) ∧ Q(x)))
    l ([∧]-intro (axPx) (axQx)) {x} = [∧]-intro (axPx{x}) (axQx{x})

    r : (∀ₗ(x ↦ P(x)) ∧ ∀ₗ(x ↦ Q(x))) ← ∀ₗ(x ↦ (P(x) ∧ Q(x)))
    r(apxqx) = [∧]-intro (\{x} → [∧]-elimₗ(apxqx{x})) (\{x} → [∧]-elimᵣ(apxqx{x}))

  [∃][∨]-distributivity : ∃(x ↦ (P(x) ∨ Q(x))) ↔ (∃(x ↦ P(x)) ∨ ∃(x ↦ Q(x)))
  [∃][∨]-distributivity = [↔]-intro l r where
    l : (∃(x ↦ P(x)) ∨ ∃(x ↦ Q(x))) → ∃(x ↦ (P(x) ∨ Q(x)))
    l ([∨]-introₗ ([∃]-intro x ⦃ px ⦄)) = [∃]-intro x ⦃ [∨]-introₗ px ⦄
    l ([∨]-introᵣ ([∃]-intro x ⦃ qx ⦄)) = [∃]-intro x ⦃ [∨]-introᵣ qx ⦄

    r : (∃(x ↦ P(x)) ∨ ∃(x ↦ Q(x))) ← ∃(x ↦ (P(x) ∨ Q(x)))
    r ([∃]-intro x ⦃ [∨]-introₗ px ⦄) = [∨]-introₗ ([∃]-intro x ⦃ px ⦄)
    r ([∃]-intro x ⦃ [∨]-introᵣ qx ⦄) = [∨]-introᵣ ([∃]-intro x ⦃ qx ⦄)

  [∃][∧]-semidistributivity : ∃(x ↦ ∃(y ↦ (P(x) ∧ Q(y)))) ↔ (∃(x ↦ P(x)) ∧ ∃(x ↦ Q(x)))
  [∃][∧]-semidistributivity = [↔]-intro l r where
    l : ∃(x ↦ ∃(y ↦ (P(x) ∧ Q(y)))) ← (∃(x ↦ P(x)) ∧ ∃(x ↦ Q(x)))
    l ([∧]-intro ([∃]-intro x ⦃ px ⦄) ([∃]-intro y ⦃ qy ⦄)) = [∃]-intro x ⦃ [∃]-intro y ⦃ [∧]-intro px qy ⦄ ⦄

    r : ∃(x ↦ ∃(y ↦ (P(x) ∧ Q(y)))) → (∃(x ↦ P(x)) ∧ ∃(x ↦ Q(x)))
    r ([∃]-intro x ⦃ [∃]-intro y ⦃ [∧]-intro px qy ⦄ ⦄) = [∧]-intro ([∃]-intro x ⦃ px ⦄) ([∃]-intro y ⦃ qy ⦄)

  [∃][∧]-distributivity : ∃(x ↦ (P(x) ∧ Q(x))) → (∃(x ↦ P(x)) ∧ ∃(x ↦ Q(x)))
  [∃][∧]-distributivity ([∃]-intro x ⦃ [∧]-intro px qx ⦄ ) = [∧]-intro l r where
    l = [∃]-intro x ⦃ px ⦄
    r = [∃]-intro x ⦃ qx ⦄

module _ {ℓₒ}{ℓₗ₁}{ℓₗ₂} {X : Type{ℓₒ}}{P : X → Stmt{ℓₗ₁}}{Q : X → Stmt{ℓₗ₂}} where
  [∀][↔]-distributivity : ∀ₗ(x ↦ (P(x) ↔ Q(x))) → (∀ₗ(x ↦ P(x)) ↔ ∀ₗ(x ↦ Q(x)))
  [∀][↔]-distributivity = r where -- [↔]-intro l r where
    -- l : ∀ₗ(x ↦ (P(x) ↔ Q(x))) ← (∀ₗ(x ↦ P(x)) ↔ ∀ₗ(x ↦ Q(x)))
    -- l([↔]-intro aqxapx apxaqx) {x} = [↔]-intro (\qx → aqxpx(qx{x})) (apxqx{x})

    r : ∀ₗ(x ↦ (P(x) ↔ Q(x))) → (∀ₗ(x ↦ P(x)) ↔ ∀ₗ(x ↦ Q(x)))
    r apxqx = [↔]-intro ([∀][→]-distributivity rl) ([∀][→]-distributivity rr) where
      rl : ∀ₗ(x ↦ (P(x) ← Q(x)))
      rl{x} = [↔]-to-[←](apxqx{x})

      rr : ∀ₗ(x ↦ (P(x) → Q(x)))
      rr{x} = [↔]-to-[→](apxqx{x})

------------------------------------------
-- Quantifiers with logical operators inside, but one of the predicates are constant

module _ {ℓₒ}{ℓₗ₁}{ℓₗ₂} {X : Type{ℓₒ}}{P : X → Stmt{ℓₗ₁}}{Q : Stmt{ℓₗ₂}} where
  [∀]-unrelatedₗ-[→] : ∀ₗ(x ↦ (P(x) → Q)) ↔ (∃(x ↦ P(x)) → Q)
  [∀]-unrelatedₗ-[→] = [↔]-intro l r where
    l : ∀ₗ(x ↦ (P(x) → Q)) ← (∃(x ↦ P(x)) → Q)
    l(expxq) {x} px = expxq([∃]-intro(x) ⦃ px ⦄)

    r : ∀ₗ(x ↦ (P(x) → Q)) → (∃(x ↦ P(x)) → Q)
    r(axpxq) = [∃]-elim(\{x} → px ↦ axpxq{x}(px))

  [∃]-unrelatedₗ-[→]ᵣ : ∃(x ↦ (P(x) → Q)) → (∀ₗ(x ↦ P(x)) → Q)
  [∃]-unrelatedₗ-[→]ᵣ = r where -- [↔]-intro l r where
    r : ∃(x ↦ (P(x) → Q)) → (∀ₗ(x ↦ P(x)) → Q)
    r(expxq)(axpx) = [∃]-proof(expxq) (axpx{[∃]-witness(expxq)})

  [∃]-unrelatedₗ-[∧] : ∃(x ↦ (P(x) ∧ Q)) ↔ (∃(x ↦ P(x)) ∧ Q)
  [∃]-unrelatedₗ-[∧] = [↔]-intro l r where
    l : ∃(x ↦ (P(x) ∧ Q)) ← (∃(x ↦ P(x)) ∧ Q)
    l ([∧]-intro ([∃]-intro x ⦃ px ⦄) q) = [∃]-intro x ⦃ [∧]-intro px q ⦄

    r : ∃(x ↦ (P(x) ∧ Q)) → (∃(x ↦ P(x)) ∧ Q)
    r ([∃]-intro x ⦃ [∧]-intro px q ⦄) = [∧]-intro ([∃]-intro x ⦃ px ⦄) q

module _ {ℓₒ}{ℓₗ₁}{ℓₗ₂} {X : Type{ℓₒ}}{P : Stmt{ℓₗ₁}}{Q : X → Stmt{ℓₗ₂}} where
  [∀]-unrelatedᵣ-[→] : ∀ₗ(x ↦ (P → Q(x))) ↔ (P → ∀ₗ(x ↦ Q(x)))
  [∀]-unrelatedᵣ-[→] = [↔]-intro l r where
    l : ∀ₗ(x ↦ (P → Q(x))) ← (P → ∀ₗ(x ↦ Q(x)))
    l(paxqx) {x} p = paxqx(p){x}

    r : ∀ₗ(x ↦ (P → Q(x))) → (P → ∀ₗ(x ↦ Q(x)))
    r(axpqx)(p){x} = axpqx{x}(p)

  [∃]-unrelatedᵣ-[→]ᵣ : ∃(x ↦ (P → Q(x))) → (P → ∃(x ↦ Q(x)))
  [∃]-unrelatedᵣ-[→]ᵣ = r where -- [↔]-intro l r where
    r : ∃(x ↦ (P → Q(x))) → (P → ∃(x ↦ Q(x)))
    r(expqx)(p) = [∃]-elim(\{x} → pqx ↦ [∃]-intro(x) ⦃ pqx(p) ⦄) (expqx)

  [∃]-unrelatedᵣ-[∧] : ∃(x ↦ (P ∧ Q(x))) ↔ (P ∧ ∃(x ↦ Q(x)))
  [∃]-unrelatedᵣ-[∧] = [↔]-intro l r where
    l : ∃(x ↦ (P ∧ Q(x))) ← (P ∧ ∃(x ↦ Q(x)))
    l ([∧]-intro p ([∃]-intro x ⦃ qx ⦄)) = [∃]-intro x ⦃ [∧]-intro p qx ⦄

    r : ∃(x ↦ (P ∧ Q(x))) → (P ∧ ∃(x ↦ Q(x)))
    r ([∃]-intro x ⦃ [∧]-intro p qx ⦄) = [∧]-intro p ([∃]-intro x ⦃ qx ⦄)

------------------------------------------
-- Other rules

module _ {ℓₒ}{ℓₗ₁}{ℓₗ₂} {X : Type{ℓₒ}}{P : X → Stmt{ℓₗ₁}}{Q : X → Stmt{ℓₗ₂}} where
  [∀][→]-add-[∃] : ∀ₗ(x ↦ (P(x) → Q(x))) → ∀ₗ(x ↦ (P(x) → ∃(x ↦ Q(x))))
  [∀][→]-add-[∃] (proof) {x} px = [∃]-intro(x) ⦃ proof{x} px ⦄

  [∀][→]-to-[∃] : ∀ₗ(x ↦ (P(x) → Q(x))) → (∃(x ↦ P(x)) → ∃(x ↦ Q(x)))
  [∀][→]-to-[∃] (proof) = ([↔]-to-[→] ([∀]-unrelatedₗ-[→] {X = X} {P})) ([∀][→]-add-[∃] (proof))

module _ {ℓₒ₁}{ℓₒ₂}{ℓₗ} {X : Type{ℓₒ₁}}{Y : Type{ℓₒ₂}}{P : X → Y → Stmt{ℓₗ}} where
  [∀][∃]-swap : ∃(x ↦ ∀ₗ(y ↦ P(x)(y))) → ∀ₗ(y ↦ ∃(x ↦ P(x)(y)))
  [∀][∃]-swap ([∃]-intro x ⦃ aypxy ⦄) {y} = [∃]-intro x ⦃ aypxy{y} ⦄

  {-
  no-intermediate : ∀{X : Stmt} → ¬(¬(X ↔ ⊤) ∧ ¬(X ↔ ⊥))
  no-intermediate = [¬][∨] [¬¬]-excluded-middle

  ¬((¬ X) ∧ (¬ Y)) ↔ ¬(¬ (X ∨ Y))
  ∀{X} → ¬¬(X ∨ (¬ X))
  -}
