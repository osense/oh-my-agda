module Format where

open import Data.Char using (Char)
open import Data.String using (String; toList; fromList; _++_)
open import Data.List hiding (_++_)
open import Data.Nat using (ℕ)
open import Data.Nat.Show


data Fmt : Set where
  nat : Fmt → Fmt
  str : Fmt → Fmt
  non : (c : Char) → Fmt → Fmt
  emp : Fmt

cover : List Char → Fmt
cover ('%' ∷ 'n' ∷ l) = nat (cover l)
cover ('%' ∷ 's' ∷ l) = str (cover l)
cover (c ∷ cs) = non c (cover cs)
cover [] = emp

type : Fmt → Set
type (nat f) = ℕ → type f
type (str f) = String → type f
type (non c f) = type f
type emp = String

helper : String → (l : Fmt) → type l
helper s (nat f) = λ n → helper (s ++ (show n)) f
helper s (str f) = λ t → helper (s ++ t) f
helper s (non c f) = helper (s ++ (fromList [ c ])) f
helper s emp = s

format : (l : String) → type (cover (toList l))
format l = helper (fromList []) (cover (toList l))


test : String
test = format "%n% of the %ss are in the %s %s" 25 "dog" "toasty" "doghouse"
