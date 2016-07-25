module Bool where


data 𝔹 : Set where ⊤ ⊥ : 𝔹

_∧_ : 𝔹 → 𝔹 → 𝔹
⊤ ∧ y = y
⊥ ∧ y = ⊥

_∨_ : 𝔹 → 𝔹 → 𝔹
⊤ ∨ _ = ⊤
⊥ ∨ y = y

if_then_else : ∀ {l} {X : Set l} → 𝔹 → X → X → X
if ⊤ then x else y = x
if ⊥ then x else y = y
