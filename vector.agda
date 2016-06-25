module vector where
open import basic

data Vec (A : Set) : ℕ → Set where
  []   : Vec A zero
  _::_ : {n : ℕ} → A →  Vec A n → Vec A (succ n)

head : {n : ℕ} → {A : Set} → Vec A (succ n) → A
head (x :: _) = x

tail : {n : ℕ} → {A : Set} → Vec A (succ n) → Vec A n
tail (_ :: xs) = xs

vec : {n : ℕ} → {A : Set} → A → Vec A n
vec {zero} x = []
vec {succ n} x = x :: vec x

vapp : {n : ℕ} → {S T : Set} → Vec (S → T) n → Vec S n → Vec T n
vapp [] [] = []
vapp (f :: fs) (s :: ss) = f s :: vapp fs ss

vmap : {n : ℕ} → {S T : Set} → (S → T) → Vec S n → Vec T n
vmap f xs = vapp (vec f) xs

zip : {n : ℕ} → {A B : Set} →  Vec A n → Vec B n → Vec (A × B) n
zip [] [] = []
zip (x :: xs) (y :: ys) = (x , y) :: zip xs ys

zip' : {n : ℕ} → {S T : Set} →  Vec S n → Vec T n → Vec (S × T) n
zip' as bs = vapp (vapp (vec _,_) as) bs

append : {n m : ℕ} → {A : Set} → Vec A n → Vec A m → Vec A (n + m)
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

concat : {n m : ℕ} → {A : Set} → Vec (Vec A m) n → Vec A (n * m)
concat [] = []
concat (xs :: xss) = append xs (concat xss)


proj : {n : ℕ} → {X : Set} → Vec X n → Fin n → X
proj (x :: xs) zero' = x
proj (x :: xs) (succ' i) = proj xs i

tabulate : {n : ℕ} → {X : Set} → (Fin n → X) → Vec X n
tabulate {zero} f = []
tabulate {succ n} f = f zero' :: tabulate (λ _ → f zero')


diagonal : {n : ℕ} → {A : Set} → Vec (Vec A n) n → Vec A n
diagonal [] = []
diagonal (xs :: xss) = head xs :: diagonal (vmap tail xss)


snoc : {n : ℕ} → {A : Set} → Vec A n → A → Vec A (succ n)
snoc [] y = y :: []
snoc (x :: xs) y = x :: snoc xs y

reverse : {n : ℕ} → {A : Set} → Vec A n → Vec A n
reverse [] = []
reverse (x :: xs) = snoc (reverse xs) x


mapp : {n m : ℕ} → {A B : Set} → Vec (Vec (A → B) n) m → Vec (Vec A n) m → Vec (Vec B n) m
mapp [] [] = []
mapp (f :: fs) (x :: xs) = vapp f x :: mapp fs xs

mapp' : {n m : ℕ} → {A B : Set} → Vec (Vec (A → B) n) n → Vec (Vec A n) n → Vec (Vec B n) n
mapp' fm xm = vapp (vapp (vec vapp) fm) xm
