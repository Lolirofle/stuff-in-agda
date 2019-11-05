import Structure.Logic.Classical.NaturalDeduction

module Structure.Logic.Classical.NaturalDeduction.Proofs {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} ⦃ classicLogic : _ ⦄ where
open Structure.Logic.Classical.NaturalDeduction.ClassicalLogic {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} (classicLogic)

open import Functional hiding (Domain)

-- TODO: Move the ones which are constructive

[↔]-with-[∧]ₗ : ∀{a₁ a₂ b} → Proof(a₁ ⟷ a₂) → Proof((a₁ ∧ b) ⟷ (a₂ ∧ b))
[↔]-with-[∧]ₗ (proof) =
  ([↔].intro
    (a₂b ↦ [∧].intro (([↔].elimₗ proof) ([∧].elimₗ a₂b)) ([∧].elimᵣ a₂b))
    (a₁b ↦ [∧].intro (([↔].elimᵣ proof) ([∧].elimₗ a₁b)) ([∧].elimᵣ a₁b))
  )

[↔]-with-[∧]ᵣ : ∀{a b₁ b₂} → Proof(b₁ ⟷ b₂) → Proof((a ∧ b₁) ⟷ (a ∧ b₂))
[↔]-with-[∧]ᵣ (proof) =
  ([↔].intro
    (ab₂ ↦ [∧].intro ([∧].elimₗ ab₂) (([↔].elimₗ proof) ([∧].elimᵣ ab₂)))
    (ab₁ ↦ [∧].intro ([∧].elimₗ ab₁) (([↔].elimᵣ proof) ([∧].elimᵣ ab₁)))
  )

[↔]-with-[∧] : ∀{a₁ a₂ b₁ b₂} → Proof(a₁ ⟷ a₂) → Proof(b₁ ⟷ b₂) → Proof((a₁ ∧ b₁) ⟷ (a₂ ∧ b₂))
[↔]-with-[∧] (a₁a₂) (b₁b₂) =
  ([↔].intro
    (a₂b₂ ↦ [∧].intro (([↔].elimₗ a₁a₂) ([∧].elimₗ a₂b₂)) (([↔].elimₗ b₁b₂) ([∧].elimᵣ a₂b₂)))
    (a₁b₁ ↦ [∧].intro (([↔].elimᵣ a₁a₂) ([∧].elimₗ a₁b₁)) (([↔].elimᵣ b₁b₂) ([∧].elimᵣ a₁b₁)))
  )

[↔]-with-[∨]ₗ : ∀{a₁ a₂ b} → Proof(a₁ ⟷ a₂) → Proof((a₁ ∨ b) ⟷ (a₂ ∨ b))
[↔]-with-[∨]ₗ (proof) =
  ([↔].intro
    ([∨].elim([∨].introₗ ∘ ([↔].elimₗ proof)) [∨].introᵣ)
    ([∨].elim([∨].introₗ ∘ ([↔].elimᵣ proof)) [∨].introᵣ)
  )

[↔]-with-[∨]ᵣ : ∀{a b₁ b₂} → Proof(b₁ ⟷ b₂) → Proof((a ∨ b₁) ⟷ (a ∨ b₂))
[↔]-with-[∨]ᵣ (proof) =
  ([↔].intro
    ([∨].elim [∨].introₗ ([∨].introᵣ ∘ ([↔].elimₗ proof)))
    ([∨].elim [∨].introₗ ([∨].introᵣ ∘ ([↔].elimᵣ proof)))
  )

[↔]-with-[∨] : ∀{a₁ a₂ b₁ b₂} → Proof(a₁ ⟷ a₂) → Proof(b₁ ⟷ b₂) → Proof((a₁ ∨ b₁) ⟷ (a₂ ∨ b₂))
[↔]-with-[∨] (a₁a₂) (b₁b₂) =
  ([↔].intro
    ([∨].elim ([∨].introₗ ∘ ([↔].elimₗ a₁a₂)) ([∨].introᵣ ∘ ([↔].elimₗ b₁b₂)))
    ([∨].elim ([∨].introₗ ∘ ([↔].elimᵣ a₁a₂)) ([∨].introᵣ ∘ ([↔].elimᵣ b₁b₂)))
  )

[↔]-with-[∀] : ∀{f g} → (∀{x} → Proof(f(x) ⟷ g(x))) → Proof((∀ₗ f) ⟷ (∀ₗ g))
[↔]-with-[∀] (proof) =
  ([↔].intro
    (allg ↦ [∀].intro(\{x} → [↔].elimₗ (proof{x}) ([∀].elim(allg){x})))
    (allf ↦ [∀].intro(\{x} → [↔].elimᵣ (proof{x}) ([∀].elim(allf){x})))
  )

[↔]-with-[∃] : ∀{f g} → (∀{x} → Proof(f(x) ⟷ g(x))) → Proof((∃ₗ f) ⟷ (∃ₗ g))
[↔]-with-[∃] (proof) =
  ([↔].intro
    ([∃].elim(\{x} → gx ↦ [∃].intro{_}{x}([↔].elimₗ (proof{x}) (gx))))
    ([∃].elim(\{x} → fx ↦ [∃].intro{_}{x}([↔].elimᵣ (proof{x}) (fx))))
  )

-- [→]-with-[∀] : ∀{p f g} → (∀{x} → Proof(f(x) ⟶ g(x))) → Proof((∀ₗ f) ⟶ (∀ₗ g))
-- [→]-with-[∀] (proof) =

-- [→]-with-[∀] : ∀{p f g} → (∀{x} → Proof(f(x) ⟶ g(x))) → Proof(∀ₗ(x ↦ p(x) ⟶ f(x))) → Proof(∀ₗ(x ↦ p(x) ⟶ g(x)))
-- [→]-with-[∀] (proof) =

[∨][∧]-distributivityₗ : ∀{a b c} → Proof((a ∨ (b ∧ c)) ⟷ (a ∨ b)∧(a ∨ c))
[∨][∧]-distributivityₗ =
  ([↔].intro
    (a∨b∧a∨c ↦
      ([∨].elim
        (a ↦ [∨].introₗ a)
        (b ↦
          ([∨].elim
            (a ↦ [∨].introₗ a)
            (c ↦ [∨].introᵣ([∧].intro b c))
            ([∧].elimᵣ a∨b∧a∨c)
          )
        )
        ([∧].elimₗ a∨b∧a∨c)
      )
    )

    (a∨b∧c ↦
      ([∨].elim
        (a   ↦ [∧].intro([∨].introₗ a)([∨].introₗ a))
        (b∧c ↦ [∧].intro([∨].introᵣ([∧].elimₗ b∧c))([∨].introᵣ([∧].elimᵣ b∧c)))
        (a∨b∧c)
      )
    )
  )

[∨][∧]-distributivityᵣ : ∀{a b c} → Proof(((a ∧ b) ∨ c) ⟷ (a ∨ c)∧(b ∨ c))
[∨][∧]-distributivityᵣ =
  ([↔].intro
    (a∨c∧b∨c ↦
      ([∨].elim
        (a ↦
          ([∨].elim
            (b ↦ [∨].introₗ([∧].intro a b))
            (c ↦ [∨].introᵣ c)
            ([∧].elimᵣ a∨c∧b∨c)
          )
        )
        (c ↦ [∨].introᵣ c)
        ([∧].elimₗ a∨c∧b∨c)
      )
    )

    (a∧b∨c ↦
      ([∨].elim
        (a∧b ↦ [∧].intro([∨].introₗ([∧].elimₗ a∧b))([∨].introₗ([∧].elimᵣ a∧b)))
        (c   ↦ [∧].intro([∨].introᵣ c)([∨].introᵣ c))
        (a∧b∨c)
      )
    )
  )

[∧][∨]-distributivityₗ : ∀{a b c} → Proof((a ∧ (b ∨ c)) ⟷ (a ∧ b)∨(a ∧ c))
[∧][∨]-distributivityₗ =
  ([↔].intro
    (a∧b∨a∧c ↦
      ([∨].elim
        (a∧b ↦ [∧].intro([∧].elimₗ a∧b)([∨].introₗ([∧].elimᵣ a∧b)))
        (a∧c ↦ [∧].intro([∧].elimₗ a∧c)([∨].introᵣ([∧].elimᵣ a∧c)))
        (a∧b∨a∧c)
      )
    )

    (a∧b∨c ↦
      ([∨].elim
        (b ↦ [∨].introₗ([∧].intro([∧].elimₗ a∧b∨c)(b)))
        (c ↦ [∨].introᵣ([∧].intro([∧].elimₗ a∧b∨c)(c)))
        ([∧].elimᵣ a∧b∨c)
      )
    )
  )

[∧][∨]-distributivityᵣ : ∀{a b c} → Proof(((a ∨ b) ∧ c) ⟷ (a ∧ c)∨(b ∧ c))
[∧][∨]-distributivityᵣ =
  ([↔].intro
    (a∧c∨b∧c ↦
      ([∨].elim
        (a∧c ↦ [∧].intro([∨].introₗ([∧].elimₗ a∧c))([∧].elimᵣ a∧c))
        (b∧c ↦ [∧].intro([∨].introᵣ([∧].elimₗ b∧c))([∧].elimᵣ b∧c))
        (a∧c∨b∧c)
      )
    )

    (a∨b∧c ↦
      ([∨].elim
        (a ↦ [∨].introₗ([∧].intro(a)([∧].elimᵣ a∨b∧c)))
        (b ↦ [∨].introᵣ([∧].intro(b)([∧].elimᵣ a∨b∧c)))
        ([∧].elimₗ a∨b∧c)
      )
    )
  )

postulate [≡]-substitute-this-is-almost-trivial : ∀{φ : Domain → Formula}{a b} → Proof(((a ≡ b) ∧ φ(a)) ⟷ φ(b))

postulate [→][∧]-distributivityₗ : ∀{X Y Z} → Proof((X ⟶ (Y ∧ Z)) ⟷ ((X ⟶ Y) ∧ (X ⟶ Z)))

postulate [∀]-unrelatedₗ-[→] : ∀{P : Domain → Formula}{Q : Formula} → Proof(∀ₗ(x ↦ (P(x) ⟶ Q)) ⟷ (∃ₗ(x ↦ P(x)) ⟶ Q))

postulate [∀]-unrelatedᵣ-[→] : ∀{P : Formula}{Q : Domain → Formula} → Proof(∀ₗ(x ↦ (P ⟶ Q(x))) ⟷ (P ⟶ ∀ₗ(x ↦ Q(x))))

postulate [∃]-unrelatedₗ-[→] : ∀{P : Domain → Formula}{Q : Formula} → Proof(∃ₗ(x ↦ (P(x) ⟶ Q)) ⟷ (∀ₗ(x ↦ P(x)) ⟶ Q))

postulate [∃]-unrelatedᵣ-[→] : ∀{P : Formula}{Q : Domain → Formula} → Proof(∃ₗ(x ↦ (P ⟶ Q(x))) ⟷ (P ⟶ ∃ₗ(x ↦ Q(x))))

-- TODO: Is equivalence unprovable? I think so
Unique-unrelatedᵣ-[→]ᵣ : ∀{P : Formula}{Q : Domain → Formula} → Proof(Unique(x ↦ (P ⟶ Q(x))) ⟶ (P ⟶ Unique(x ↦ Q(x))))
Unique-unrelatedᵣ-[→]ᵣ {P}{Q} =
  [→].intro(uniquepq ↦ [→].intro(p ↦ [∀].intro(\{x} → [∀].intro(\{y} → [→].intro(qxqy ↦
    ([→].elim
      ([∀].elim([∀].elim uniquepq{x}){y})
      (([↔].elimᵣ [→][∧]-distributivityₗ) ([→].intro(p ↦ qxqy)))
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
  ([→].intro(proof ↦
    ([↔].elimₗ [→][∧]-distributivityₗ)
    ([∧].intro
      (([↔].elimᵣ [∃]-unrelatedᵣ-[→])    ([∧].elimₗ proof))
      (([→].elim Unique-unrelatedᵣ-[→]ᵣ) ([∧].elimᵣ proof))
    )
  ))

-- TODO: I think this is similar to the skolemization process of going from ∀∃ to ∃function∀
[∃]-fn-witness : ∀{P : Domain → Domain → Formula} → ⦃ _ : Proof(∀ₗ(x ↦ ∃ₗ(y ↦ P(x)(y)))) ⦄ → Domain → Domain
[∃]-fn-witness{P} ⦃ proof ⦄ (x) = [∃]-witness ⦃ [∀].elim(proof){x} ⦄

[∃]-fn-proof : ∀{P : Domain → Domain → Formula} → ⦃ p : Proof(∀ₗ(x ↦ ∃ₗ(y ↦ P(x)(y)))) ⦄ → Proof(∀ₗ(x ↦ P(x)([∃]-fn-witness{P} ⦃ p ⦄ (x))))
[∃]-fn-proof{P} ⦃ proof ⦄ =
  ([∀].intro(\{x} →
    [∃]-proof {P(x)} ⦃ [∀].elim proof{x} ⦄
  ))

[∃!]-fn-witness : ∀{P : Domain → Domain → Formula} → ⦃ _ : Proof(∀ₗ(x ↦ ∃ₗ!(y ↦ P(x)(y)))) ⦄ → Domain → Domain
[∃!]-fn-witness{P} ⦃ proof ⦄ (x) = [∃!]-witness ⦃ [∀].elim(proof){x} ⦄

{-
[∃!]-fn-proof : ∀{P : Domain → Domain → Formula} → ⦃ p : Proof(∀ₗ(x ↦ ∃ₗ!(y ↦ P(x)(y)))) ⦄ → Proof(∀ₗ(x ↦ P(x)([∃!]-fn-witness{P} ⦃ p ⦄ (x))))
[∃!]-fn-proof{P} ⦃ proof ⦄ =
  ([∀].intro(\{x} →
    [∃!]-proof {P(x)} ⦃ [∀].elim proof{x} ⦄
  ))
-}

[∃!]-fn-proof : ∀{P : Domain → Domain → Formula} → ⦃ p : Proof(∀ₗ(x ↦ ∃ₗ!(y ↦ P(x)(y)))) ⦄ → ∀{x} → Proof(P(x)([∃!]-fn-witness{P} ⦃ p ⦄ (x)))
[∃!]-fn-proof{P} ⦃ proof ⦄ {x} =
  [∃!]-proof {P(x)} ⦃ [∀].elim proof{x} ⦄

postulate [∃!]-fn-unique : ∀{P : Domain → Domain → Formula} → ⦃ p : Proof(∀ₗ(x ↦ ∃ₗ!(y ↦ P(x)(y)))) ⦄ → ∀{x} → Proof(∀ₗ(y ↦ P(x)(y) ⟶ (y ≡ [∃!]-fn-witness{P} ⦃ p ⦄ (x))))
