--
-- Reduced words. Every equivalence class in the free group has a unique fully reduced word.
--
-- Findind this fully reduced word is possibe, but needs the underlying Setoid to have decidable equalit

open import Relation.Binary
open import Level

module NormalForm {c ℓ} (S : DecSetoid c ℓ) where

open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; refl; inspect)
import Relation.Binary.EqReasoning
open import Data.Product hiding (map)
open import Function
open import Data.List
open import Data.List.Properties
open import Relation.Nullary

open import Generators
import FreeGroups
open module F = FreeGroups (DecSetoid.setoid S)

-- Decidable equality on generators
open DecSetoid (Generators.decSetoid S) using (_≟_; _≈_)

Reduced : Word → Set _
Reduced x = ∄ (λ y → RedTo x y)

_∷f_ : G → Word → Word
_∷f_ g [] = g ∷ []
_∷f_ g (x ∷ xs) with g ≟ invert₁ x
... | yes p = xs
... | no ¬p = g ∷ x ∷ xs

tailReduced : ∀{x xs} → Reduced (x ∷ xs) → Reduced xs
tailReduced {x} p (.(xs ++ ys) , reds xs x' ys) = p ((x ∷ xs ++ ys) , (reds (x ∷ xs) x' ys))

consReduced : ∀{x y ys l} → ¬ x ≈ invert₁ y → Reduced (y ∷ ys) → l ≡ x ∷ y ∷ ys → Reduced l
consReduced {x} {y} ¬e _ eq (.ys' , reds [] x' ys') = ¬e $
  begin x ≡⟨ P.sym eq1 ⟩ invert₁ x' ≡⟨ P.cong _ eq2 ⟩ invert₁ y ∎
  where eq1 = proj₁ (∷-injective eq)
        eq2 = proj₁ (∷-injective (proj₂ (∷-injective eq)))
        open Relation.Binary.EqReasoning (Generators.setoid (DecSetoid.setoid S))
consReduced ¬e ¬r eq (.(x' ∷ xs ++ ys) , reds (x' ∷ xs) x0 ys) with ∷-injective eq
... | (eq1 , eq2) =  ¬r (xs ++ ys , (
               P.subst (λ y → RedTo y (xs ++ ys)) eq2 $
               P.subst (λ y → RedTo (xs ++ invert₁ x0 ∷ x0 ∷ ys) (xs ++ ys)) eq1 $
               reds xs x0 ys))

lem-[]-red' : ∀{xs} → xs ≡ [] → Reduced xs
lem-[]-red' () (.ys , reds [] x ys)
lem-[]-red' () (.(x ∷ xs ++ ys) , reds (x ∷ xs) x' ys)

lem-[]-red : Reduced []
lem-[]-red = lem-[]-red' refl

lem-[x]-red' : ∀{xs} (x : G) → xs ≡ [ x ] → Reduced xs
lem-[x]-red' _ () (.ys , reds [] x' ys)
lem-[x]-red' _ () (.(x' ∷ ys) , reds (x' ∷ []) x0 ys)
lem-[x]-red' _ () (.(x' ∷ x0 ∷ xs ++ ys) , reds (x' ∷ x0 ∷ xs) x1 ys)

lem-[x]-red : (x : G) → Reduced [ x ]
lem-[x]-red x = lem-[x]-red' x refl


lem-∷f : ∀{x xs} → Reduced xs → Reduced (x ∷f xs)
lem-∷f {xs = []} _ = lem-[x]-red _
lem-∷f {x} {xs = y ∷ ys} r with x ≟ invert₁ y
... | yes _ = tailReduced r
... | no ¬p  = consReduced ¬p r P.refl


normalize : Word → Word
normalize l = foldr _∷f_ [] l

lem-normalized : (xs : List G) → Reduced (normalize xs)
lem-normalized [] = lem-[]-red
lem-normalized (x ∷ xs) = lem-∷f (lem-normalized xs)
