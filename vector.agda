module vector where
open import basic

data Vec (A : Set) : ℕ → Set where
  []   : Vec A zero
  _::_ : {n : ℕ} → A →  Vec A n → Vec A (succ n)

head : ∀ {n A} → Vec A (succ n) → A
head (x :: _) = x

tail : ∀ {n A} -> Vec A (succ n) → Vec A n
tail (_ :: xs) = xs

vec : ∀ {n A} → A → Vec A n
vec {zero} x = []
vec {succ n} x = x :: vec x

vapp : ∀ {n S T} → Vec (S → T) n → Vec S n → Vec T n
vapp [] [] = []
vapp (f :: fs) (s :: ss) = f s :: vapp fs ss

vmap : ∀ {n S T} → (S → T) → Vec S n → Vec T n
vmap f xs = vapp (vec f) xs

zip : ∀ {n A B} → Vec A n → Vec B n → Vec (A × B) n
zip [] [] = []
zip (x :: xs) (y :: ys) = (x , y) :: zip xs ys

zip' : ∀ {n S T} → Vec S n → Vec T n → Vec (S × T) n
zip' as bs = vapp (vapp (vec _,_) as) bs

append : ∀ {n m A} → Vec A n → Vec A m → Vec A (n + m)
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

concat : ∀ {n m A} → Vec (Vec A m) n → Vec A (n * m)
concat [] = []
concat (xs :: xss) = append xs (concat xss)


proj : ∀ {n X} → Vec X n → Fin n → X
proj (x :: xs) zero' = x
proj (x :: xs) (succ' i) = proj xs i

tabulate : ∀ {n X} → (Fin n → X) → Vec X n
tabulate {zero} f = []
tabulate {succ n} f = f zero' :: tabulate (λ _ → f zero')


diagonal : ∀ {n A} → Vec (Vec A n) n → Vec A n
diagonal [] = []
diagonal (xs :: xss) = head xs :: diagonal (vmap tail xss)


snoc : ∀ {n A} → Vec A n → A → Vec A (succ n)
snoc [] y = y :: []
snoc (x :: xs) y = x :: snoc xs y

reverse : ∀ {A n} → Vec A n → Vec A n
reverse [] = []
reverse (x :: xs) = snoc (reverse xs) x

-- I think we need to declare something like (n ≤ m) first here
--diagonal' : ∀ {A n m} → Vec (Vec A m) n → Vec A n
--diagonal' [] = []
--diagonal' {n = succ n} (xs :: xss) = {!proj (reverse xs) (fin n) :: diagonal' {n = n} xss!}
