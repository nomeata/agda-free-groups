open import Relation.Binary

module FreeGroups {c ℓ} (S : Setoid c ℓ) where

open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; refl; inspect)
import Relation.Binary.List.Pointwise as LP
import Relation.Binary.EqReasoning
open import Data.Product hiding (map)
open import Function
open import Relation.Binary
import Data.Bool
open import Data.List
open import Data.List.Properties
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Data.Empty
import Algebra.FunctionProperties as FP
open import Algebra

open import Generators

-- 
-- G is the set of generators (and their inverses)
-- Word are the elements of the free group
--

G : Set c
G = Setoid.Carrier (setoid S)

Word : Set c
Word = List G

--
-- We define a reduction relation, representing the cancellation
-- of two adjacent elements in a word.
--

data RedTo : Rel Word c where
   reds : (xs : Word) → (x : G) → (ys : Word) → RedTo (xs ++ invert₁ x ∷ x ∷ ys) (xs ++ ys)

--
-- This cancellation is respected by list concatenation.
--

lem-++-red1 : (zs : Word) → RedTo =[ (λ xs → xs ++ zs) ]⇒ RedTo
lem-++-red1 zs (reds xs x ys) = P.subst₂ RedTo
  (P.sym (Monoid.assoc (monoid G) xs (invert₁ x ∷ x ∷ ys) zs))
  (P.sym (Monoid.assoc (monoid G) xs ys zs))
  (reds xs x (ys ++ zs))

lem-++-red2 : (zs : Word) → RedTo =[ (λ xs → zs ++ xs) ]⇒ RedTo
lem-++-red2 zs (reds xs x ys) = P.subst₂ RedTo
  (Monoid.assoc (monoid G) zs xs (invert₁ x ∷ x ∷ ys))
  (Monoid.assoc (monoid G) zs xs ys)
  (reds (zs ++ xs) x ys)

--
-- The equivalence relation that the free groups are based on is
-- the equivalence hull of the reduction relation.
--

_≈f_ : Rel (Word) _
_≈f_ = EqCl RedTo

--
-- Inverting a word, which is involutive, commutes with append
-- and respected the reduction relation
--

inv : Word → Word
inv x = reverse (Data.List.map invert₁ x)

inv-inv : FP.Involutive _≡_ inv
inv-inv x = begin
  inv (inv x)
      ≡⟨ P.cong reverse (reverse-map-commute invert₁ (map invert₁ x)) ⟩
  reverse (reverse (map invert₁ (map invert₁ x)))
      ≡⟨ reverse-inv (map invert₁ (map invert₁ x)) ⟩
  map invert₁ (map invert₁ x)
      ≡⟨ P.sym (map-compose x) ⟩
  map (invert₁ ∘ invert₁) x
      ≡⟨ map-cong invert₁-inv x ⟩
  map id x
      ≡⟨ map-id x ⟩
  x ∎
  where open P.≡-Reasoning

inv-++-commute : (xs ys : Word) → (inv ys ++ inv xs ≡ inv (xs ++ ys))
inv-++-commute xs ys = begin
  inv ys ++ inv xs
    ≡⟨ P.sym (reverse-++-commute (map invert₁ xs) (map invert₁ ys)) ⟩
  reverse (map invert₁ xs ++ map invert₁ ys)
    ≡⟨ P.sym (P.cong reverse (map-++-commute invert₁ xs ys)) ⟩ 
  inv (xs ++ ys) ∎
  where open P.≡-Reasoning

lem-inv-red : RedTo =[ inv ]⇒ RedTo
lem-inv-red (reds xs x ys) = P.subst₂ RedTo p1 p2 (reds (inv ys) x (inv xs))
  where
    open P.≡-Reasoning
    p1 = begin
      inv ys ++ invert₁ x ∷ x ∷ inv xs
        ≡⟨ P.sym $ P.cong (λ y → inv ys ++ invert₁ x ∷ y ∷ inv xs) $ invert₁-inv x ⟩
      inv ys ++ invert₁ x ∷ invert₁ (invert₁ x) ∷ inv xs
        ≡⟨ P.sym $ Monoid.assoc (monoid G) (inv ys) [ invert₁ x ] $ invert₁ (invert₁ x) ∷ inv xs ⟩
      (inv ys ++ [ invert₁ x ]) ++ invert₁ (invert₁ x) ∷ inv xs
        ≡⟨ P.cong (λ y → y ++ invert₁ (invert₁ x) ∷ inv xs) $ inv-++-commute [ x ] ys ⟩
      inv (x ∷ ys) ++ invert₁ (invert₁ x) ∷ inv xs
        ≡⟨ P.sym $ Monoid.assoc (monoid G) (inv (x ∷ ys)) [ invert₁ (invert₁ x)] (inv xs) ⟩
      (inv (x ∷ ys) ++ [ invert₁ (invert₁ x) ]) ++ inv xs
        ≡⟨ P.cong (λ y → y ++ inv xs) $ inv-++-commute [ invert₁ x ] (x ∷ ys) ⟩
      inv (invert₁ x ∷ x ∷ ys) ++ inv xs
        ≡⟨ inv-++-commute xs (invert₁ x ∷ x ∷ ys) ⟩
      inv (xs ++ invert₁ x ∷ x ∷ ys)
        ∎
    p2 = inv-++-commute xs ys

--
-- Here, we define the actual group and check the group axioms
--

group : Group _ _ 
group = record {
  Carrier = Word;
  _≈_ = _≈f_;
  _∙_ = _++_;
  ε = [];
  _⁻¹ = inv;
  isGroup = record {
    isMonoid = record {
      isSemigroup = record {
        isEquivalence = L.isEquivalence;
        assoc = λ x y z → L.reflexive (Monoid.assoc (monoid G) x y z);
        ∙-cong = cong1
      };
      identity = (λ x → L.refl) , (λ x → L.reflexive (proj₂ (Monoid.identity (monoid G)) x))
    };
    inverse = linv , rinv;
    ⁻¹-cong = mapEq lem-inv-red
    }
  }
  where
  module L = Setoid (eqSetoid RedTo)

  cong1 : {x y u v : Word} → x ≈f y → u ≈f v → (x ++ u) ≈f (y ++ v)
  cong1 {x} {y} {u} {v} p1 p2 = begin
    x ++ u
      ≈⟨ mapEq (lem-++-red1 u) p1 ⟩
    y ++ u
      ≈⟨ mapEq (lem-++-red2 y) p2 ⟩
    y ++ v
      ∎
    where
      open Relation.Binary.EqReasoning (eqSetoid RedTo)

  linv : FP.LeftInverse _≈f_ [] inv _++_
  linv [] = reflEq
  linv (x ∷ xs) = begin
    inv (x ∷ xs) ++ x ∷ xs
      ≡⟨ P.sym (P.cong (λ y → y ++ x ∷ xs) (inv-++-commute [ x ] xs)) ⟩
    (inv xs ++ [ invert₁ x ]) ++ x ∷ xs
      ≡⟨ Monoid.assoc (monoid G) (inv xs) [ invert₁ x ] (x ∷ xs) ⟩
    inv xs ++ invert₁ x ∷ x ∷ xs
      ≈⟨ impEq (reds (inv xs) x xs) ⟩
    inv xs ++ xs
      ≈⟨ linv xs ⟩
    [] ∎
    where open Relation.Binary.EqReasoning (eqSetoid RedTo)

  rinv : FP.RightInverse _≈f_ [] inv _++_
  rinv x = begin
    x ++ inv x
      ≡⟨ P.cong (λ y → y ++ inv x) (P.sym (inv-inv x)) ⟩
    inv (inv x) ++ inv x
      ≈⟨ linv (inv x) ⟩
    [] ∎
    where open  Relation.Binary.EqReasoning (eqSetoid RedTo)
