module HeytingAlgebra where

open import Algebra using (DistributiveLattice; BooleanAlgebra)
open import Algebra.Structures using (IsDistributiveLattice)
open import Algebra.FunctionProperties using (Op₁; Op₂)
open import Relation.Binary using (Rel)
open import Data.Product using (proj₁; proj₂)
open import Level


record HeytingAlgebra c l : Set (suc (c ⊔ l)) where
  infix  8 ¬_
  infixr 7 _∧_
  infixr 6 _∨_
  infixr 5 _⇒_
  infix  4 _≈_

  field
    Carrier : Set c
    _≈_     : Rel Carrier l
    _∧_     : Op₂ Carrier
    _∨_     : Op₂ Carrier
    _⇒_     : Op₂ Carrier
    ¬_      : Op₁ Carrier
    ⊤ ⊥     : Carrier

    isDistributiveLattice : IsDistributiveLattice _≈_ _∨_ _∧_
    impl-id   : ∀ {a} → (a ⇒ a) ≈ ⊤
    ∧-dist₁   : ∀ {a b} → (a ∧ (a ⇒ b)) ≈ (a ∧ b)
    ∧-dist₂   : ∀ {a b} → (b ∧ (a ⇒ b)) ≈ b
    ⇒-dist    : ∀ {a b c} → (a ⇒ (b ∧ c)) ≈ ((a ⇒ b) ∧ (a ⇒ c))

  _≥_ : Rel Carrier l
  a ≥ b = a ⇒ b ≈ ⊤


-- Every Boolean algebra is a Heyting algebra.
boolean-is-heyting : ∀ {a l} → BooleanAlgebra a l → HeytingAlgebra a l
boolean-is-heyting {a} {l} b = record
  {Carrier = Carrier
  ;_≈_ = _≈_
  ;_∧_ = _∧_
  ;_∨_ = _∨_
  ;_⇒_ = λ a b → (¬ a) ∨ b
  ;¬_ = ¬_
  ;⊤ = ⊤
  ;⊥ = ⊥
  ;isDistributiveLattice = isDistributiveLattice
  ;impl-id = λ {a} → trans (∨-comm (¬ a) a)
                           (∨-complementʳ a)
  ;∧-dist₁ = λ {a} {b} → trans (∧-∨-distribˡ a (¬ a) b)
                               (trans (∨-cong (∧-complementʳ a) refl)
                                      (∨-identity (a ∧ b)))
  ;∧-dist₂ = λ {a} {b} → trans (∧-cong refl (∨-comm (¬ a) b))
                               ((proj₂ absorptive) b (¬ a))
  ;⇒-dist = λ {a} {b} {c} → ∨-∧-distribˡ (¬ a) b c}
    where open BooleanAlgebra b
          BDist = record {Carrier = Carrier; _≈_ = _≈_; _∨_ = _∨_; _∧_ = _∧_; isDistributiveLattice = isDistributiveLattice}
          open import Algebra.Properties.DistributiveLattice (BDist) using (∧-∨-distrib; ∨-∧-distrib)
          ∧-∨-distribˡ = proj₁ ∧-∨-distrib
          ∨-∧-distribˡ = proj₁ ∨-∧-distrib
          open import Algebra.Properties.BooleanAlgebra (b) using (∧-∨-commutativeSemiring; ∧-∨-isCommutativeSemiring)
          ∨-identity = proj₁ (Algebra.CommutativeSemiring.*-identity ∧-∨-commutativeSemiring)
