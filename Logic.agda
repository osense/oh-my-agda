module Logic where

data _∧_ (P : Set) (Q : Set) : Set where
  ∧-int : P → Q → (P ∧ Q)

∧-elim₁ : {P Q : Set} → (P ∧ Q) → P
∧-elim₁ (∧-int p q) = p

∧-elim₂ : {P Q : Set} → (P ∧ Q) → Q
∧-elim₂ (∧-int p q) = q

∧-comm' : {P Q : Set} → (P ∧ Q) → (Q ∧ P)
∧-comm' (∧-int p q) = ∧-int q p


_⇔_ : (P : Set) → (Q : Set) → Set
p ⇔ q = (p → q) ∧ (q → p)

∧-comm : {P Q : Set} → (P ∧ Q) ⇔ (Q ∧ P)
∧-comm = ∧-int ∧-comm' ∧-comm'


∧-assoc¹ : {P Q R : Set} → (P ∧ (Q ∧ R)) → ((P ∧ Q) ∧ R)
∧-assoc¹ (∧-int p (∧-int q r)) = ∧-int (∧-int p q) r

∧-assoc² : {P Q R : Set} → ((P ∧ Q) ∧ R) → (P ∧ (Q ∧ R)) 
∧-assoc² (∧-int (∧-int p q) r) = ∧-int p (∧-int q r)

∧-assoc : {P Q R : Set} → (P ∧ (Q ∧ R)) ⇔ ((P ∧ Q) ∧ R)
∧-assoc = ∧-int ∧-assoc¹ ∧-assoc²

data _∨_ (P : Set) (Q : Set) : Set where
  ∨-int₁ : P → (P ∨ Q)
  ∨-int₂ : Q → (P ∨ Q)

∨-elim : {P Q R : Set} → (P → R) → (Q → R) → (P ∨ Q) → R
∨-elim f _ (∨-int₁ p) = f p
∨-elim _ g (∨-int₂ q) = g q


abs₁ : {P Q : Set} → (P ∧ (P ∨ Q)) ⇔ P
abs₁ = ∧-int ∧-elim₁
             (λ p → ∧-int p (∨-int₁ p))

id : {A : Set} → A → A
id x = x

abs₂ : {P Q : Set} → (P ∨ (P ∧ Q)) ⇔ P
abs₂ = ∧-int (∨-elim id ∧-elim₁)
             ∨-int₁


distrib₁¹ : {P Q R : Set} → (P ∧ (Q ∨ R)) → ((P ∧ Q) ∨ (P ∧ R))
distrib₁¹ (∧-int p (∨-int₁ q)) = ∨-int₁ (∧-int p q)
distrib₁¹ (∧-int p (∨-int₂ r)) = ∨-int₂ (∧-int p r)

distrib₁² : {P Q R : Set} → ((P ∧ Q) ∨ (P ∧ R)) → (P ∧ (Q ∨ R))
distrib₁² (∨-int₁ (∧-int p q)) = ∧-int p (∨-int₁ q)
distrib₁² (∨-int₂ (∧-int p r)) = ∧-int p (∨-int₂ r)

distrib₁ : {P Q R : Set} → (P ∧ (Q ∨ R)) ⇔ ((P ∧ Q) ∨ (P ∧ R))
distrib₁ = ∧-int distrib₁¹ distrib₁²


distrib₂¹ : {P Q R : Set} → (P ∨ (Q ∧ R)) → ((P ∨ Q) ∧ (P ∨ R))
distrib₂¹ (∨-int₁ p) = ∧-int (∨-int₁ p) (∨-int₁ p)
distrib₂¹ (∨-int₂ (∧-int q r)) = ∧-int (∨-int₂ q) (∨-int₂ r)

distrib₂² : {P Q R : Set} → ((P ∨ Q) ∧ (P ∨ R)) → (P ∨ (Q ∧ R))
distrib₂² (∧-int (∨-int₁ p) _) = ∨-int₁ p
distrib₂² (∧-int _ (∨-int₁ p)) = ∨-int₁ p
distrib₂² (∧-int (∨-int₂ q) (∨-int₂ r)) = ∨-int₂ (∧-int q r)

distrib₂ : {P Q R : Set} → (P ∨ (Q ∧ R)) ⇔ ((P ∨ Q) ∧ (P ∨ R))
distrib₂ = ∧-int distrib₂¹ distrib₂²
