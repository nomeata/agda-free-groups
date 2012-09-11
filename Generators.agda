module Generators where

open import Level
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; refl; inspect)
import Relation.Binary.List.Pointwise as LP
open import Function
open import Relation.Binary
open import Data.List
open import Data.List.Properties
open import Relation.Nullary
import Algebra.FunctionProperties as FP

-- Free Groups are built upon sets of generators. These can occur directly
-- or as their abstract inverse:

data Gen {c} (A : Set c) : Set c where
  gen : A → Gen A
  gen-inv : A → Gen A

-- Inverting one generator is an involutive operation.

invert₁ : ∀{a} → {A : Set a} → Gen A → Gen A
invert₁ (gen x) = (gen-inv x)
invert₁ (gen-inv x) = (gen x)

invert₁-inv : ∀{a} {A : Set a} → FP.Involutive _≡_ (invert₁ {a} {A})
invert₁-inv (gen x) = refl
invert₁-inv (gen-inv x) = refl

-- An equivalence relation (setoid, decidable setoid) of the underlying
-- setinduces an equivalence relation (setoid, decidable setoid) on the generators.

data LiftGen {a ℓ} {A : Set a} (_~_ : Rel A ℓ) : Gen A → Gen A → Set (a ⊔ ℓ)  where
  gen : {x y : A} → (x ~ y) → LiftGen _~_ (gen x) (gen y)
  gen-inv : {x y : A } → (x ~ y) → LiftGen _~_ (gen-inv x) (gen-inv y)

unLiftGen : ∀{a ℓ} {A : Set a} {_~_ : Rel A ℓ} {a b : _} →
  LiftGen _~_ (gen a) (gen b) → a ~ b
unLiftGen (gen y) = y

unLiftGenInv : ∀{a ℓ} {A : Set a} {_~_ : Rel A ℓ} {a b : _} →
  LiftGen _~_ (gen-inv a) (gen-inv b) → a ~ b
unLiftGenInv (gen-inv y) = y

genIsDec : ∀{a ℓ} {A : Set a} { _~_ : Rel A ℓ} → Decidable _~_ →
  Decidable (LiftGen _~_)
genIsDec d (gen a) (gen b) with d a b 
... | yes p = yes (gen p)
... | no p = no (p ∘ unLiftGen)
genIsDec d (gen a) (gen-inv b) = no (λ ())
genIsDec d (gen-inv a) (gen b) = no (λ ())
genIsDec d (gen-inv a) (gen-inv b) with d a b
... | yes p = yes (gen-inv p)
... | no p = no (p ∘ unLiftGenInv)

genIsEquivalence : ∀{a ℓ} {A : Set a} { _~_ : Rel A ℓ} → IsEquivalence _~_ →
  IsEquivalence (LiftGen _~_)
genIsEquivalence {_} {_} {A} {_~_} e =
  record  { refl = r ; sym = sym ; trans = trans }
  where module E = IsEquivalence e
        _≈_ = LiftGen _~_ 
    
        r : {x : Gen A} → LiftGen _~_ x x
        r {gen y} = gen E.refl
        r {gen-inv y} = gen-inv E.refl
  
        sym : ∀ {x y} → LiftGen _~_ x y → LiftGen _~_ y x
        sym (gen p) = gen (E.sym p)
        sym (gen-inv p) = gen-inv (E.sym p)

        trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
        trans (gen p1) (gen p2) = gen (E.trans p1 p2)
        trans (gen-inv p1) (gen-inv p2) = gen-inv (E.trans p1 p2)


genIsDecEquivalence : ∀{a ℓ} {A : Set a} {_≈_ : Rel A ℓ} → IsDecEquivalence _≈_ →
  IsDecEquivalence (LiftGen _≈_)
genIsDecEquivalence d = record {
  isEquivalence = genIsEquivalence (IsDecEquivalence.isEquivalence d);
  _≟_ = genIsDec (IsDecEquivalence._≟_ d)
  }

setoid : ∀{a ℓ} → Setoid a ℓ → Setoid _ _
setoid s = record {
  isEquivalence = genIsEquivalence (Setoid.isEquivalence s)
  }

decSetoid : ∀{a ℓ} → DecSetoid a ℓ → DecSetoid _ _
decSetoid d = record {
  isDecEquivalence = genIsDecEquivalence (DecSetoid.isDecEquivalence d)
  }

--
-- Transitive reflexive symmetric hull of a relation. Ought to go to some standard library
--

data EqCl {c ℓ} {A : Set c} (R : Rel {c} A ℓ) : Rel A ℓ where
  impEq : R ⇒ EqCl R
  symEq : Symmetric (EqCl R)
  reflEq : Reflexive (EqCl R)
  transEq : Trans (EqCl R) (EqCl R) (EqCl R)

eqSetoid : ∀{ℓ} → {A : Set ℓ} → (_⟶_ : Rel A ℓ) → Setoid _ _
eqSetoid  _⟶_ = record {
  _≈_ = EqCl _⟶_;
  isEquivalence = record { refl = reflEq ; sym = symEq ; trans = transEq}
  }

--
-- A function that respects the underlying relation also respects its transitive
-- reflexive symmetric hull.
--

liftEqCl : ∀{c d ℓ ℓ2} → {A : Set c} → {B : Setoid d ℓ} → {T : Rel A ℓ2} → {f : A → Setoid.Carrier B } → T =[ f ]⇒ Setoid._≈_ B → EqCl T =[ f ]⇒ Setoid._≈_ B
liftEqCl p (impEq y) = p y
liftEqCl {B = B} p (symEq y) = Setoid.sym B (liftEqCl {B = B} p y)
liftEqCl {B = B} p reflEq = Setoid.refl B
liftEqCl {B = B} p (transEq y y') = Setoid.trans B (liftEqCl {B = B} p y) (liftEqCl {B = B} p y')

mapEq : ∀{ℓ} → {A : Set ℓ} → {T : Rel A ℓ} → {f : A → A } →
      T =[ f ]⇒ T → EqCl T =[ f ]⇒ EqCl T
mapEq {T = T} p = liftEqCl {B = eqSetoid T} (impEq ∘ p)

--
-- Utility lemmata that went into the standard library, but has not released yet.
--

reverse-map-commute :
  ∀ {a b} {A : Set a} {B : Set b} (f : A → B) → (xs : List A) →
  map f (reverse xs) ≡ reverse (map f xs)
reverse-map-commute f [] = refl
reverse-map-commute f (x ∷ xs) = begin
  map f (reverse (x ∷ xs))
    ≡⟨ P.cong (map f) (unfold-reverse x xs) ⟩
  map f (reverse xs ∷ʳ x)
    ≡⟨ map-++-commute f (reverse xs) (x ∷ []) ⟩
  map f (reverse xs) ∷ʳ f x
    ≡⟨ P.cong (λ y → y ∷ʳ f x) (reverse-map-commute f xs) ⟩
  reverse (map f xs) ∷ʳ f x
    ≡⟨ P.sym (unfold-reverse (f x) (map f xs)) ⟩
  reverse (map f (x ∷ xs))
    ∎
  where
    open P.≡-Reasoning

reverse-inv : ∀{a} {A : Set a} → FP.Involutive {_} {_} {List A} _≡_ reverse
reverse-inv [] = refl
reverse-inv (x ∷ xs) = begin
  reverse (reverse (x ∷ xs))
    ≡⟨ P.cong reverse (unfold-reverse x xs) ⟩
  reverse (reverse xs ∷ʳ x)
    ≡⟨ reverse-++-commute (reverse xs) (x ∷ []) ⟩
  x ∷ reverse (reverse (xs))
    ≡⟨ P.cong (λ y → x ∷ y) (reverse-inv xs) ⟩
  x ∷ xs
    ∎
  where
    open P.≡-Reasoning



