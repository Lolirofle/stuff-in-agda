import Structure.Logic.Classical.NaturalDeduction

module Structure.Logic.Classical.NaturalDeduction.Proofs {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} {ℓₘₒ} {Object} {obj} ⦃ sign : _ ⦄ ⦃ theory : _ ⦄ where
private module PredicateEq = Structure.Logic.Classical.NaturalDeduction.PredicateEq {ℓₗ} {Formula} {ℓₘₗ} (Proof) {ℓₒ} (Domain) {ℓₘₒ} {Object} (obj)
open PredicateEq.Signature(sign)
open PredicateEq.Theory(theory)

open import Functional hiding (Domain)

-- TODO: Move the ones which are constructive

postulate excluded-middle : ∀{a} → Proof(a ∨ (¬ a))

[↔]-with-[∧]ₗ : ∀{a₁ a₂ b} → Proof(a₁ ⟷ a₂) → Proof((a₁ ∧ b) ⟷ (a₂ ∧ b))
[↔]-with-[∧]ₗ (proof) =
  ([↔]-intro
    (a₂b ↦ [∧]-intro (([↔]-elimₗ proof) ([∧]-elimₗ a₂b)) ([∧]-elimᵣ a₂b))
    (a₁b ↦ [∧]-intro (([↔]-elimᵣ proof) ([∧]-elimₗ a₁b)) ([∧]-elimᵣ a₁b))
  )

[↔]-with-[∧]ᵣ : ∀{a b₁ b₂} → Proof(b₁ ⟷ b₂) → Proof((a ∧ b₁) ⟷ (a ∧ b₂))
[↔]-with-[∧]ᵣ (proof) =
  ([↔]-intro
    (ab₂ ↦ [∧]-intro ([∧]-elimₗ ab₂) (([↔]-elimₗ proof) ([∧]-elimᵣ ab₂)))
    (ab₁ ↦ [∧]-intro ([∧]-elimₗ ab₁) (([↔]-elimᵣ proof) ([∧]-elimᵣ ab₁)))
  )

[↔]-with-[∧] : ∀{a₁ a₂ b₁ b₂} → Proof(a₁ ⟷ a₂) → Proof(b₁ ⟷ b₂) → Proof((a₁ ∧ b₁) ⟷ (a₂ ∧ b₂))
[↔]-with-[∧] (a₁a₂) (b₁b₂) =
  ([↔]-intro
    (a₂b₂ ↦ [∧]-intro (([↔]-elimₗ a₁a₂) ([∧]-elimₗ a₂b₂)) (([↔]-elimₗ b₁b₂) ([∧]-elimᵣ a₂b₂)))
    (a₁b₁ ↦ [∧]-intro (([↔]-elimᵣ a₁a₂) ([∧]-elimₗ a₁b₁)) (([↔]-elimᵣ b₁b₂) ([∧]-elimᵣ a₁b₁)))
  )

[↔]-with-[∨]ₗ : ∀{a₁ a₂ b} → Proof(a₁ ⟷ a₂) → Proof((a₁ ∨ b) ⟷ (a₂ ∨ b))
[↔]-with-[∨]ₗ (proof) =
  ([↔]-intro
    ([∨]-elim([∨]-introₗ ∘ ([↔]-elimₗ proof)) [∨]-introᵣ)
    ([∨]-elim([∨]-introₗ ∘ ([↔]-elimᵣ proof)) [∨]-introᵣ)
  )

[↔]-with-[∨]ᵣ : ∀{a b₁ b₂} → Proof(b₁ ⟷ b₂) → Proof((a ∨ b₁) ⟷ (a ∨ b₂))
[↔]-with-[∨]ᵣ (proof) =
  ([↔]-intro
    ([∨]-elim [∨]-introₗ ([∨]-introᵣ ∘ ([↔]-elimₗ proof)))
    ([∨]-elim [∨]-introₗ ([∨]-introᵣ ∘ ([↔]-elimᵣ proof)))
  )

[↔]-with-[∨] : ∀{a₁ a₂ b₁ b₂} → Proof(a₁ ⟷ a₂) → Proof(b₁ ⟷ b₂) → Proof((a₁ ∨ b₁) ⟷ (a₂ ∨ b₂))
[↔]-with-[∨] (a₁a₂) (b₁b₂) =
  ([↔]-intro
    ([∨]-elim ([∨]-introₗ ∘ ([↔]-elimₗ a₁a₂)) ([∨]-introᵣ ∘ ([↔]-elimₗ b₁b₂)))
    ([∨]-elim ([∨]-introₗ ∘ ([↔]-elimᵣ a₁a₂)) ([∨]-introᵣ ∘ ([↔]-elimᵣ b₁b₂)))
  )

[↔]-with-[∀] : ∀{f g} → (∀{x} → Proof(f(obj x) ⟷ g(obj x))) → Proof((∀ₗ f) ⟷ (∀ₗ g))
[↔]-with-[∀] (proof) =
  ([↔]-intro
    (allg ↦ [∀]-intro(\{x} → [↔]-elimₗ (proof{x}) ([∀]-elim(allg){x})))
    (allf ↦ [∀]-intro(\{x} → [↔]-elimᵣ (proof{x}) ([∀]-elim(allf){x})))
  )

[↔]-with-[∃] : ∀{f g} → (∀{x} → Proof(f(obj x) ⟷ g(obj x))) → Proof((∃ₗ f) ⟷ (∃ₗ g))
[↔]-with-[∃] (proof) =
  ([↔]-intro
    ([∃]-elim(\{x} → gx ↦ [∃]-intro{_}{x}([↔]-elimₗ (proof{x}) (gx))))
    ([∃]-elim(\{x} → fx ↦ [∃]-intro{_}{x}([↔]-elimᵣ (proof{x}) (fx))))
  )

postulate [∨][∧]-distributivityₗ : ∀{a b c} → Proof((a ∨ (b ∧ c)) ⟷ (a ∨ b)∧(a ∨ c))
postulate [∨][∧]-distributivityᵣ : ∀{a b c} → Proof(((a ∧ b) ∨ c) ⟷ (a ∨ c)∧(b ∨ c))
postulate [∧][∨]-distributivityₗ : ∀{a b c} → Proof((a ∧ (b ∨ c)) ⟷ (a ∧ b)∨(a ∧ c))
postulate [∧][∨]-distributivityᵣ : ∀{a b c} → Proof(((a ∨ b) ∧ c) ⟷ (a ∧ c)∨(b ∧ c))
postulate [≡]-substitute-this-is-almost-trivial : ∀{φ : Domain → Formula}{a b} → Proof(((a ≡ b) ∧ φ(a)) ⟷ φ(b))

postulate [→][∧]-distributivityₗ : ∀{X Y Z} → Proof((X ⟶ (Y ∧ Z)) ⟷ ((X ⟶ Y) ∧ (X ⟶ Z)))

postulate [∀]-unrelatedₗ-[→] : ∀{P : Domain → Formula}{Q : Formula} → Proof(∀ₗ(x ↦ (P(x) ⟶ Q)) ⟷ (∃ₗ(x ↦ P(x)) ⟶ Q))

postulate [∀]-unrelatedᵣ-[→] : ∀{P : Formula}{Q : Domain → Formula} → Proof(∀ₗ(x ↦ (P ⟶ Q(x))) ⟷ (P ⟶ ∀ₗ(x ↦ Q(x))))

postulate [∃]-unrelatedₗ-[→] : ∀{P : Domain → Formula}{Q : Formula} → Proof(∃ₗ(x ↦ (P(x) ⟶ Q)) ⟷ (∀ₗ(x ↦ P(x)) ⟶ Q))

postulate [∃]-unrelatedᵣ-[→] : ∀{P : Formula}{Q : Domain → Formula} → Proof(∃ₗ(x ↦ (P ⟶ Q(x))) ⟷ (P ⟶ ∃ₗ(x ↦ Q(x))))

-- TODO: Is equivalence unprovable? I think so
Unique-unrelatedᵣ-[→]ᵣ : ∀{P : Formula}{Q : Domain → Formula} → Proof(Unique(x ↦ (P ⟶ Q(x))) ⟶ (P ⟶ Unique(x ↦ Q(x))))
Unique-unrelatedᵣ-[→]ᵣ {P}{Q} =
  [→]-intro(uniquepq ↦ [→]-intro(p ↦ [∀]-intro(\{x} → [∀]-intro(\{y} → [→]-intro(qxqy ↦
    ([→]-elim
      ([∀]-elim([∀]-elim uniquepq{x}){y})
      (([↔]-elimᵣ [→][∧]-distributivityₗ) ([→]-intro(p ↦ qxqy)))
    )
  )))))
  -- Proving these equivalent:
  -- ∀ₗ(x ↦ ∀ₗ(y ↦ (P ⟶ Q(x)) ∧ (P ⟶ Q(y)) ⟶ (x ≡ y))
  -- P ⟶ ∀ₗ(x ↦ ∀ₗ(y ↦ Q(x) ∧ Q(y) ⟶ (x ≡ y))
    -- test : Proof(∀ₗ(x ↦ ∀ₗ(y ↦ (P ⟶ Q(x)) ∧ (P ⟶ Q(y)) ⟶ (x ≡ y))) ⟷ ∀ₗ(x ↦ ∀ₗ(y ↦ (P ⟶ Q(x) ∧ Q(y)) ⟶ (x ≡ y))))
    -- test = ([↔]-with-[∀] ([↔]-with-[∀] ([→][∧]-distributivityₗ)))

-- TODO: Is left provable? Above left seems unprovable
[∃!]-unrelatedᵣ-[→]ᵣ : ∀{P : Formula}{Q : Domain → Formula} → Proof(∃ₗ!(x ↦ (P ⟶ Q(x))) ⟶ (P ⟶ ∃ₗ!(x ↦ Q(x))))
[∃!]-unrelatedᵣ-[→]ᵣ {P}{Q} =
  ([→]-intro(proof ↦
    ([↔]-elimₗ [→][∧]-distributivityₗ)
    ([∧]-intro
      (([↔]-elimᵣ [∃]-unrelatedᵣ-[→])    ([∧]-elimₗ proof))
      (([→]-elim Unique-unrelatedᵣ-[→]ᵣ) ([∧]-elimᵣ proof))
    )
  ))

-- TODO: I think this is similar to the skolemization process of going from ∀∃ to ∃function∀
[∃]-fn-witness : ∀{P : Domain → Domain → Formula} → ⦃ _ : Proof(∀ₗ(x ↦ ∃ₗ(y ↦ P(x)(y)))) ⦄ → Object → Object
[∃]-fn-witness{P} ⦃ proof ⦄ (x) = [∃]-witness ⦃ [∀]-elim(proof){x} ⦄

-- TODO: But this works with axiom of choice, so it is alright. Just assume that (Object → Domain) is surjective, which it should be!. For boundedPredEqSignature to work, one needs to prove that the composition of surjective functions is surjective, and then that Σ.elem is surjective, which it should be because (Σ.elem: ΣA B → A), and it gives one such A for every A and every proof there is of B
{-
[∃]-fn-proof : ∀{P : Domain → Domain → Formula} → ⦃ p : Proof(∀ₗ(x ↦ ∃ₗ(y ↦ P(x)(y)))) ⦄ → Proof(∀ₗ(x ↦ P(x)([∃]-fn-witness{P} ⦃ p ⦄ (x))))
[∃]-fn-proof{P} ⦃ proof ⦄ =
  ([∀]-intro(\{x} →
    [∃]-proof {P(x)} ⦃ [∀]-elim proof{x} ⦄
  ))
-}

[∃]-fn-proof : ∀{P : Domain → Domain → Formula} → ⦃ p : Proof(∀ₗ(x ↦ ∃ₗ(y ↦ P(x)(y)))) ⦄ → ∀{x} → Proof(P(obj x)(obj([∃]-fn-witness{P} ⦃ p ⦄ (x))))
[∃]-fn-proof{P} ⦃ proof ⦄ {x} =
  [∃]-proof {P(obj x)} ⦃ [∀]-elim proof{x} ⦄

[∃!]-fn-witness : ∀{P : Domain → Domain → Formula} → ⦃ _ : Proof(∀ₗ(x ↦ ∃ₗ!(y ↦ P(x)(y)))) ⦄ → Object → Object
[∃!]-fn-witness{P} ⦃ proof ⦄ (x) = [∃!]-witness ⦃ [∀]-elim(proof){x} ⦄

{-
[∃!]-fn-proof : ∀{P : Domain → Domain → Formula} → ⦃ p : Proof(∀ₗ(x ↦ ∃ₗ!(y ↦ P(x)(y)))) ⦄ → Proof(∀ₗ(x ↦ P(x)([∃!]-fn-witness{P} ⦃ p ⦄ (x))))
[∃!]-fn-proof{P} ⦃ proof ⦄ =
  ([∀]-intro(\{x} →
    [∃!]-proof {P(x)} ⦃ [∀]-elim proof{x} ⦄
  ))
-}

[∃!]-fn-proof : ∀{P : Domain → Domain → Formula} → ⦃ p : Proof(∀ₗ(x ↦ ∃ₗ!(y ↦ P(x)(y)))) ⦄ → ∀{x} → Proof(P(obj x)(obj([∃!]-fn-witness{P} ⦃ p ⦄ (x))))
[∃!]-fn-proof{P} ⦃ proof ⦄ {x} =
  [∃!]-proof {P(obj x)} ⦃ [∀]-elim proof{x} ⦄

postulate [∃!]-fn-unique : ∀{P : Domain → Domain → Formula} → ⦃ p : Proof(∀ₗ(x ↦ ∃ₗ!(y ↦ P(x)(y)))) ⦄ → ∀{x} → Proof(∀ₗ(y ↦ P(obj x)(y) ⟶ (y ≡ obj([∃!]-fn-witness{P} ⦃ p ⦄ (x)))))
