module Logic.Predicate.Theorems {ℓ₁} {ℓ₂} where

import      Lvl
open import Functional
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Logic.Propositional.Theorems{ℓ₁ Lvl.⊔ ℓ₂}
open import Logic.Predicate{ℓ₁}{ℓ₂}
open import Type

[∀]-swap : ∀{X Y}{P : X → Y → Stmt} → ∀ₗ(x ↦ ∀ₗ(y ↦ P(x)(y))) → ∀ₗ(y ↦ ∀ₗ(x ↦ P(x)(y)))
[∀]-swap(xypxy){y}{x} = xypxy{x}{y}

[∃]-swap : ∀{X Y}{P : X → Y → Stmt} → ∃(x ↦ ∃(y ↦ P(x)(y))) → ∃(y ↦ ∃(x ↦ P(x)(y)))
[∃]-swap([∃]-intro(x) ⦃ [∃]-intro(y) ⦃ proof ⦄ ⦄) = [∃]-intro(y) ⦃ [∃]-intro(x) ⦃ proof ⦄ ⦄

[∃]-irrelevant : ∀{X}{P : Stmt} → ∃{X}(x ↦ P) → P
[∃]-irrelevant([∃]-intro(_) ⦃ proof ⦄) = proof

-- Note:
--   The following is unprovable:
--   [∀]-irrelevant : ∀{X}{P : Stmt} → ∀ₗ{X}(x ↦ P) → P
--   X is not guaranteed to not be the empty type, and even if it was, the ∀ function requires a constructed value. It seems to need a non-empty domain to quantify over.
[∀ₑ]-irrelevant : ∀{X}{P : Stmt} → ∀ₑ{X}(x ↦ P) → P
[∀ₑ]-irrelevant = [∀ₑ]-elimₑ

[∀][∃¬]-contradiction : ∀{X}{P : X → Stmt} → ∀ₗ(x ↦ P(x)) → ∃(x ↦ ¬(P(x))) → ⊥
[∀][∃¬]-contradiction{X}{P} (ap)(enp) =
  ([∃]-elim(\{a} → np ↦ (
    ([⊥]-intro
      ([∀]-elim{X}{P} ap(a))
      np
    )
  )) (enp))

[∀]-to-[¬∃¬] : ∀{X}{P : X → Stmt} → ∀ₗ(x ↦ P(x)) → (¬ ∃(x ↦ ¬(P(x))))
[∀]-to-[¬∃¬] = [∀][∃¬]-contradiction -- [∃]-elim(\{a} → npa ↦ npa(p{a}))(ep)

[∃¬]-to-[¬∀] : ∀{X}{P : X → Stmt} → (∃(x ↦ ¬(P(x)))) → (¬ ∀{x} → P(x))
[∃¬]-to-[¬∀] = swap [∀][∃¬]-contradiction

{-TODO
[¬∀ₑ]-to-[∃¬] : ∀{X}{P : X → Stmt} → (∃(x ↦ ¬(P(x)))) ← (¬ ∀ₑ(x → P(x)))
[¬∀ₑ]-to-[∃¬] {X}{_} (a) (napx) =
  ([∃]-intro(a)
    ⦃ [¬]-intro(pa ↦
        ([∀]-intro(pa))
        (napx)
      )
    ⦄
  )
-}

[∀¬¬][∃¬]-contradiction : ∀{X}{P : X → Stmt} → ∀ₗ(x ↦ ¬¬(P(x))) → (∃(x ↦ ¬(P(x)))) → ⊥
[∀¬¬][∃¬]-contradiction{X}{P} (annp)([∃]-intro(a) ⦃ na ⦄) =
  [∀][∃¬]-contradiction{X}{¬¬_ ∘ P} (annp)([∃]-intro(a) ⦃ [¬¬]-intro(na) ⦄)

[∀¬¬]-to-[¬∃¬] : ∀{X}{P : X → Stmt} → ∀ₗ(x ↦ ¬¬(P(x))) → (¬ ∃(x ↦ ¬(P(x))))
[∀¬¬]-to-[¬∃¬] = [∀¬¬][∃¬]-contradiction

[¬¬∀]-to-[¬∃¬] : ∀{X}{P : X → Stmt} → ¬¬ ∀ₗ(x ↦ (P(x))) → (¬ ∃(x ↦ ¬(P(x))))
[¬¬∀]-to-[¬∃¬] = contrapositiveᵣ [∃¬]-to-[¬∀]
-- [¬¬∀]-to-[¬∃¬] (annx) (enx) =
--   ([⊥]-intro
--     ([∃¬]-to-[¬∀](enx))
--     (annx)
--   )

[¬∃¬]-to-[∀¬¬] : ∀{X}{P : X → Stmt} → ¬(∃(x ↦ ¬(P(x)))) → ∀ₗ(x ↦ ¬¬(P(x)))
[¬∃¬]-to-[∀¬¬] {X}{P} (nenx) {a} (npa) = nenx([∃]-intro(a) ⦃ npa ⦄)

[¬¬∀]-to-[∀¬¬] : ∀{X}{P : X → Stmt} → ¬¬ ∀ₗ(x ↦ (P(x))) → ∀ₗ(x ↦ ¬¬(P(x)))
[¬¬∀]-to-[∀¬¬] = [¬∃¬]-to-[∀¬¬] ∘ [¬¬∀]-to-[¬∃¬]

-- TODO: Probably unprovable because people said so. Not sure why. Maybe because (¬¬A is valid in constructive logic) ⇔ (A is valid in classical logic), and therefore this would not be possible because everything here is in constructive logic.
-- [∀¬¬]-to-[¬¬∀] : ∀{X}{P : X → Stmt} → ¬¬∀ₗ(x ↦ (P(x))) ← ∀ₗ(x ↦ ¬¬(P(x)))

[∀¬]-to-[¬∃] : ∀{X}{P : X → Stmt} → ∀ₗ(x ↦ ¬(P(x))) → ¬(∃(x ↦ P(x)))
[∀¬]-to-[¬∃] (anpx) =
  ([¬]-intro(epx ↦
    [∃]-elim(\{a} → pa ↦
      ([⊥]-intro
        pa
        (anpx{a})
      )
    )(epx)
  ))

[¬∃]-to-[∀¬] : ∀{X}{P : X → Stmt} → ∀ₗ(x ↦ ¬(P(x))) ← ¬(∃(x ↦ P(x)))
[¬∃]-to-[∀¬] {X}{P} (nepx) =
  ([∀]-intro(a ↦
    (([¬]-intro(pa ↦
      (([⊥]-intro
        (([∃]-intro a ⦃ pa ⦄) :of: (∃(x ↦ P(x))))
        (nepx :of: ¬(∃(x ↦ P(x))))
      ) :of: ⊥)
    )) :of: ¬(P(a)))
  ))

-- TODO: Probably unprovable because [∀]-elim seems to need a constructed element?
-- [∀]-to-[∃] : ∀{X}{P : X → Stmt} → ∀(x ↦ P(x)) → ∃(x ↦ P(x))

[∀ₑ]-to-[∃] : ∀{X}{P : X → Stmt} → ∀ₑ(x ↦ P(x)) → ∃(x ↦ P(x))
[∀ₑ]-to-[∃] (apx) =
  [∃]-intro(_) ⦃ [∀ₑ]-elimₑ(apx) ⦄

[∀][→]-distributivity : ∀{X}{P Q : X → Stmt} → ∀ₗ(x ↦ (P(x) → Q(x))) → ∀ₗ(x ↦ P(x)) → ∀ₗ(x ↦ Q(x))
[∀][→]-distributivity (PxQx) (Px) = PxQx(Px)

[∀][∧]-distributivity : ∀{X}{P Q : X → Stmt} → (∀ₗ(x ↦ P(x)) ∧ ∀ₗ(x ↦ Q(x))) ↔ ∀ₗ(x ↦ (P(x) ∧ Q(x)))
[∀][∧]-distributivity {X}{P}{Q} = [↔]-intro l r where
  l : (∀ₗ(x ↦ P(x)) ∧ ∀ₗ(x ↦ Q(x))) ← ∀ₗ(x ↦ (P(x) ∧ Q(x)))
  l(apxqx) = [∧]-intro (\{x} → [∧]-elimₗ(apxqx{x})) (\{x} → [∧]-elimᵣ(apxqx{x}))

  r : (∀ₗ(x ↦ P(x)) ∧ ∀ₗ(x ↦ Q(x))) → ∀ₗ(x ↦ (P(x) ∧ Q(x)))
  r ([∧]-intro (axPx) (axQx)) {x} = [∧]-intro (axPx{x}) (axQx{x})

[∃][∨]-distributivity : ∀{X}{P Q : X → Stmt} → (∃(x ↦ P(x)) ∨ ∃(x ↦ Q(x))) ↔ ∃(x ↦ (P(x) ∨ Q(x)))
[∃][∨]-distributivity {X}{P}{Q} = [↔]-intro l r where
  l : (∃(x ↦ P(x)) ∨ ∃(x ↦ Q(x))) ← ∃(x ↦ (P(x) ∨ Q(x)))
  l ([∃]-intro x ⦃ [∨]-introₗ px ⦄) = [∨]-introₗ ([∃]-intro x ⦃ px ⦄)
  l ([∃]-intro x ⦃ [∨]-introᵣ qx ⦄) = [∨]-introᵣ ([∃]-intro x ⦃ qx ⦄)

  r : (∃(x ↦ P(x)) ∨ ∃(x ↦ Q(x))) → ∃(x ↦ (P(x) ∨ Q(x)))
  r ([∨]-introₗ ([∃]-intro x ⦃ px ⦄)) = [∃]-intro x ⦃ [∨]-introₗ px ⦄
  r ([∨]-introᵣ ([∃]-intro x ⦃ qx ⦄)) = [∃]-intro x ⦃ [∨]-introᵣ qx ⦄

[∀]-unrelatedₗ-[→] : ∀{X}{P : X → Stmt}{Q : Stmt} → ∀ₗ(x ↦ (P(x) → Q)) ↔ (∃(x ↦ P(x)) → Q)
[∀]-unrelatedₗ-[→] {X}{P}{Q} = [↔]-intro l r where
  l : ∀ₗ(x ↦ (P(x) → Q)) ← (∃(x ↦ P(x)) → Q)
  l(expxq) {x} px = expxq([∃]-intro(x) ⦃ px ⦄)

  r : ∀ₗ(x ↦ (P(x) → Q)) → (∃(x ↦ P(x)) → Q)
  r(axpxq) = [∃]-elim(\{x} → px ↦ axpxq{x}(px))

[∀]-unrelatedᵣ-[→] : ∀{X}{P : Stmt}{Q : X → Stmt} → ∀ₗ(x ↦ (P → Q(x))) ↔ (P → ∀ₗ(x ↦ Q(x)))
[∀]-unrelatedᵣ-[→] {X}{P}{Q} = [↔]-intro l r where
  l : ∀ₗ(x ↦ (P → Q(x))) ← (P → ∀ₗ(x ↦ Q(x)))
  l(paxqx) {x} p = paxqx(p){x}

  r : ∀ₗ(x ↦ (P → Q(x))) → (P → ∀ₗ(x ↦ Q(x)))
  r(axpqx)(p){x} = axpqx{x}(p)

[∃]-unrelatedₗ-[→]ᵣ : ∀{X}{P : X → Stmt}{Q : Stmt} → ∃(x ↦ (P(x) → Q)) → (∀ₗ(x ↦ P(x)) → Q)
[∃]-unrelatedₗ-[→]ᵣ {X}{P}{Q} = r where -- [↔]-intro l r where
  -- TODO: Would this work with ∀ₑ?
  -- l : ∃(x ↦ (P(x) → Q)) ← (∀ₗ(x ↦ P(x)) → Q)
  -- l(axpxq) = [∃]-intro(_) ⦃ px ↦ axpxq(px) ⦄

  r : ∃(x ↦ (P(x) → Q)) → (∀ₗ(x ↦ P(x)) → Q)
  r(expxq)(axpx) = [∃]-proof(expxq) (axpx{[∃]-witness(expxq)})

[∃]-unrelatedᵣ-[→]ᵣ : ∀{X}{P : Stmt}{Q : X → Stmt} → ∃(x ↦ (P → Q(x))) → (P → ∃(x ↦ Q(x)))
[∃]-unrelatedᵣ-[→]ᵣ {X}{P}{Q} = r where -- [↔]-intro l r where
  -- TODO: Where should the p come from when applying [∃]-intro?
  -- l : ∃(x ↦ (P → Q(x))) ← (P → ∃(x ↦ Q(x)))
  -- l(pexqx) = [∃]-intro([∃]-witness(pexqx(p))) ⦃ _ ↦ [∃]-proof(pexqx(p)) ⦄ where
  --   postulate p : P

  r : ∃(x ↦ (P → Q(x))) → (P → ∃(x ↦ Q(x)))
  r(expqx)(p) = [∃]-elim(\{x} → pqx ↦ [∃]-intro(x) ⦃ pqx(p) ⦄) (expqx)

[∃]-unrelatedₗ-[∧] : ∀{X}{P : X → Stmt}{Q : Stmt} → ∃(x ↦ (P(x) ∧ Q)) ↔ (∃(x ↦ P(x)) ∧ Q)
[∃]-unrelatedₗ-[∧] {X}{P}{Q} = [↔]-intro l r where
  l : ∃(x ↦ (P(x) ∧ Q)) ← (∃(x ↦ P(x)) ∧ Q)
  l ([∧]-intro ([∃]-intro x ⦃ px ⦄) q) = [∃]-intro x ⦃ [∧]-intro px q ⦄

  r : ∃(x ↦ (P(x) ∧ Q)) → (∃(x ↦ P(x)) ∧ Q)
  r ([∃]-intro x ⦃ [∧]-intro px q ⦄) = [∧]-intro ([∃]-intro x ⦃ px ⦄) q


[∃]-unrelatedᵣ-[∧] : ∀{X}{P : Stmt}{Q : X → Stmt} → ∃(x ↦ (P ∧ Q(x))) ↔ (P ∧ ∃(x ↦ Q(x)))
[∃]-unrelatedᵣ-[∧] {X}{P}{Q} = [↔]-intro l r where
  l : ∃(x ↦ (P ∧ Q(x))) ← (P ∧ ∃(x ↦ Q(x)))
  l ([∧]-intro p ([∃]-intro x ⦃ qx ⦄)) = [∃]-intro x ⦃ [∧]-intro p qx ⦄

  r : ∃(x ↦ (P ∧ Q(x))) → (P ∧ ∃(x ↦ Q(x)))
  r ([∃]-intro x ⦃ [∧]-intro p qx ⦄) = [∧]-intro p ([∃]-intro x ⦃ qx ⦄)

[∃][∧]-semidistributivity : ∀{X}{P : X → Stmt}{Q : X → Stmt} → ∃(x ↦ ∃(y ↦ (P(x) ∧ Q(y)))) ↔ (∃(x ↦ P(x)) ∧ ∃(x ↦ Q(x)))
[∃][∧]-semidistributivity {X}{P}{Q} = [↔]-intro l r where
  l : ∃(x ↦ ∃(y ↦ (P(x) ∧ Q(y)))) ← (∃(x ↦ P(x)) ∧ ∃(x ↦ Q(x)))
  l ([∧]-intro ([∃]-intro x ⦃ px ⦄) ([∃]-intro y ⦃ qy ⦄)) = [∃]-intro x ⦃ [∃]-intro y ⦃ [∧]-intro px qy ⦄ ⦄

  r : ∃(x ↦ ∃(y ↦ (P(x) ∧ Q(y)))) → (∃(x ↦ P(x)) ∧ ∃(x ↦ Q(x)))
  r ([∃]-intro x ⦃ [∃]-intro y ⦃ [∧]-intro px qy ⦄ ⦄) = [∧]-intro ([∃]-intro x ⦃ px ⦄) ([∃]-intro y ⦃ qy ⦄)

[∃][∧]-distributivity : ∀{X}{P : X → Stmt}{Q : X → Stmt} → ∃(x ↦ (P(x) ∧ Q(x))) → (∃(x ↦ P(x)) ∧ ∃(x ↦ Q(x)))
[∃][∧]-distributivity {X}{P}{Q} ([∃]-intro x ⦃ [∧]-intro px qx ⦄ ) = [∧]-intro l r where
  l = [∃]-intro x ⦃ px ⦄
  r = [∃]-intro x ⦃ qx ⦄

[∀][↔]-distributivity : ∀{X}{P Q : X → Stmt} → ∀ₗ(x ↦ (P(x) ↔ Q(x))) → (∀ₗ(x ↦ P(x)) ↔ ∀ₗ(x ↦ Q(x)))
[∀][↔]-distributivity {X}{P}{Q} = r where -- [↔]-intro l r where
  -- l : ∀ₗ(x ↦ (P(x) ↔ Q(x))) ← (∀ₗ(x ↦ P(x)) ↔ ∀ₗ(x ↦ Q(x)))
  -- l([↔]-intro aqxapx apxaqx) {x} = [↔]-intro (\qx → aqxpx(qx{x})) (apxqx{x})

  r : ∀ₗ(x ↦ (P(x) ↔ Q(x))) → (∀ₗ(x ↦ P(x)) ↔ ∀ₗ(x ↦ Q(x)))
  r apxqx = [↔]-intro ([∀][→]-distributivity rl) ([∀][→]-distributivity rr) where
    rl : ∀ₗ(x ↦ (P(x) ← Q(x)))
    rl{x} = [↔]-elimₗ(apxqx{x})

    rr : ∀ₗ(x ↦ (P(x) → Q(x)))
    rr{x} = [↔]-elimᵣ(apxqx{x})

[∀][→]-add-[∃] : ∀{X}{P Q : X → Stmt} → ∀ₗ(x ↦ (P(x) → Q(x))) → ∀ₗ(x ↦ (P(x) → ∃(x ↦ Q(x))))
[∀][→]-add-[∃] (proof) {x} px = [∃]-intro(x) ⦃ proof{x} px ⦄

[∀][→]-to-[∃] : ∀{X}{P Q : X → Stmt} → ∀ₗ(x ↦ (P(x) → Q(x))) → (∃(x ↦ P(x)) → ∃(x ↦ Q(x)))
[∀][→]-to-[∃] {X} {P}{Q} (proof) = ([↔]-elimᵣ ([∀]-unrelatedₗ-[→] {X} {P})) ([∀][→]-add-[∃] (proof))

[∀][∃]-swap : ∀{X Y}{P : X → Y → Stmt} → ∃(x ↦ ∀ₗ(y ↦ P(x)(y))) → ∀ₗ(y ↦ ∃(x ↦ P(x)(y)))
[∀][∃]-swap ([∃]-intro x ⦃ aypxy ⦄) {y} = [∃]-intro x ⦃ aypxy{y} ⦄

{-
no-intermediate : ∀{X : Stmt} → ¬(¬(X ↔ ⊤) ∧ ¬(X ↔ ⊥))
no-intermediate = [¬][∨] [¬¬]-excluded-middle

¬((¬ X) ∧ (¬ Y)) ↔ ¬(¬ (X ∨ Y))
∀{X} → ¬¬(X ∨ (¬ X))
-}
