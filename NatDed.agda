module Logic where

data _∧_ (P : Set) (Q : Set) : Set where
  _,_ : P → Q → (P ∧ Q)

∧-elim₁ : {P Q : Set} → (P ∧ Q) → P
∧-elim₁ (p , q) = p

∧-elim₂ : {P Q : Set} → (P ∧ Q) → Q
∧-elim₂ (p , q) = q

∧-comm' : {P Q : Set} → (P ∧ Q) → (Q ∧ P)
∧-comm' (p , q) = (q , p)


_⇔_ : (P : Set) → (Q : Set) → Set
p ⇔ q = (p → q) ∧ (q → p)

∧-comm : {P Q : Set} → (P ∧ Q) ⇔ (Q ∧ P)
∧-comm = (∧-comm' , ∧-comm')


∧-assoc¹ : {P Q R : Set} → (P ∧ (Q ∧ R)) → ((P ∧ Q) ∧ R)
∧-assoc¹ (p , (q , r)) = ((p , q) , r)

∧-assoc² : {P Q R : Set} → ((P ∧ Q) ∧ R) → (P ∧ (Q ∧ R)) 
∧-assoc² ((p , q) , r) = (p , (q , r))

∧-assoc : {P Q R : Set} → (P ∧ (Q ∧ R)) ⇔ ((P ∧ Q) ∧ R)
∧-assoc = (∧-assoc¹ , ∧-assoc²)

data _∨_ (P : Set) (Q : Set) : Set where
  left : P → (P ∨ Q)
  right : Q → (P ∨ Q)

∨-elim : {P Q R : Set} → (P → R) → (Q → R) → (P ∨ Q) → R
∨-elim f _ (left p) = f p
∨-elim _ g (right q) = g q


abs₁ : {P Q : Set} → (P ∧ (P ∨ Q)) ⇔ P
abs₁ = (∧-elim₁ , λ p → (p , left p))

abs₂ : {P Q : Set} → (P ∨ (P ∧ Q)) ⇔ P
abs₂ = (∨-elim (λ x → x) ∧-elim₁ , left)


distrib₁¹ : {P Q R : Set} → (P ∧ (Q ∨ R)) → ((P ∧ Q) ∨ (P ∧ R))
distrib₁¹ (p , (left q)) = left (p , q)
distrib₁¹ (p , (right r)) = right (p , r)

distrib₁² : {P Q R : Set} → ((P ∧ Q) ∨ (P ∧ R)) → (P ∧ (Q ∨ R))
distrib₁² (left (p , q)) = p , (left q)
distrib₁² (right (p , r)) = p , (right r)

distrib₁ : {P Q R : Set} → (P ∧ (Q ∨ R)) ⇔ ((P ∧ Q) ∨ (P ∧ R))
distrib₁ = (distrib₁¹ , distrib₁²)


distrib₂¹ : {P Q R : Set} → (P ∨ (Q ∧ R)) → ((P ∨ Q) ∧ (P ∨ R))
distrib₂¹ (left p) = (left p , left p)
distrib₂¹ (right (q , r)) = (right q , right r)

distrib₂² : {P Q R : Set} → ((P ∨ Q) ∧ (P ∨ R)) → (P ∨ (Q ∧ R))
distrib₂² ((left p) , _) = left p
distrib₂² (_ , (left p)) = left p
distrib₂² ((right q) , (right r)) = right (q , r)

distrib₂ : {P Q R : Set} → (P ∨ (Q ∧ R)) ⇔ ((P ∨ Q) ∧ (P ∨ R))
distrib₂ = (distrib₂¹ , distrib₂²)
