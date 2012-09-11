module UnivProp where

open import FreeGroups
open import GroupHom
open import Relation.Binary
open import Algebra
open import Function.Equality hiding (cong)
open import Data.List
open import Generators
open import Data.Product hiding (map)
import Relation.Binary.EqReasoning as EqR

appGen : ∀{c ℓ} → {A : Setoid c ℓ} → {B : Group c ℓ} → (f : A ⟶ Group.setoid B) → Gen (Setoid.Carrier A) → Group.Carrier B
appGen f (gen y) = f ⟨$⟩ y
appGen {B = B} f (gen-inv y) = (f ⟨$⟩ y)⁻¹ where open Group B

gConcat : ∀{c ℓ} → {B : Group c ℓ} → List (Group.Carrier B) → Group.Carrier B
gConcat {B = B} = foldr _∙_ ε where open Group B

[_]* : ∀{c ℓ} → {A : Setoid c ℓ} → {B : Group c ℓ} → (f : A ⟶ Group.setoid B) → group A -Group→ B
[_]* {c} {ℓ} {A} {B} f = record {
     ⟦_⟧ = f*;
     ⟦⟧-cong = cong;
     ∙-homo = homo  }
     where
     open Group (group A) renaming (_∙_ to _∙₁_; _≈_ to _≈₁_)
     open Group B renaming (_∙_ to _∙₂_; _≈_ to _≈₂_; ∙-cong to ∙₂-cong;
          refl to refl₂; sym to sym₂; assoc to assoc₂;
          ε to ε₂; inverse to inverse₂; identity to identity₂)
     f* : Word A → Group.Carrier B
     f* = λ x → gConcat {B = B} (map (appGen {B = B} f) x)
     
     open EqR (Group.setoid B)

     homo : (x y : Word A) → f* (x ∙₁ y) ≈₂ (f* x ∙₂ f* y)
     homo [] y = Group.sym B (proj₁ (Group.identity B) _)
     homo (x ∷ xs) y =
       begin
         f* ((x ∷ xs) ∙₁ y)
       ≈⟨ refl₂ ⟩
         appGen {B = B} f x ∙₂ f* (xs ∙₁ y)
       ≈⟨ ∙₂-cong refl₂ (homo xs y)  ⟩
         appGen {B = B} f x ∙₂ (f* xs ∙₂ f* y)
       ≈⟨ sym₂ (assoc₂ _ _ _) ⟩
         (appGen {B = B} f x ∙₂ f* xs) ∙₂ f* y
       ≈⟨ refl₂ ⟩
         f* (x ∷ xs) ∙₂ f* y
       ∎

     appGenCancel : ∀{x} → appGen {B = B} f (invert₁ x) ∙₂ appGen {B = B} f x ≈₂ ε₂
     appGenCancel {gen y} = proj₁ inverse₂ _
     appGenCancel {gen-inv y} = proj₂ inverse₂ _

     cong' : {i j : Word A} → RedTo A i j → f* i ≈₂ f* j
     cong' (reds xs x ys) =
       begin
         f* (xs ++ invert₁ x ∷ x ∷ ys)
       ≈⟨ homo xs _ ⟩
         f* xs ∙₂ f* (invert₁ x ∷ x ∷ ys)
       ≈⟨ refl₂ ⟩
         f* xs ∙₂ (appGen {B = B} f (invert₁ x) ∙₂ (appGen {B = B} f x ∙₂ f* ys))
       ≈⟨ ∙₂-cong refl₂ (sym₂ (assoc₂ _ _ _)) ⟩
         f* xs ∙₂ ((appGen {B = B} f (invert₁ x) ∙₂ appGen {B = B} f x) ∙₂ f* ys)
       ≈⟨ ∙₂-cong refl₂ (∙₂-cong (appGenCancel {x}) refl₂) ⟩
         f* xs ∙₂ (ε₂ ∙₂ f* ys)
       ≈⟨ ∙₂-cong refl₂ (proj₁ identity₂ _) ⟩
         f* xs ∙₂ f* ys
       ≈⟨ Group.sym B (homo xs _) ⟩
         f* (xs ++ ys)
       ∎

     cong : f* Preserves _≈₁_ ⟶ _≈₂_
     cong = liftEqCl {B = Group.setoid B} {f = f*} cong'

lift-uniq :
  ∀{c ℓ} → {A : Setoid c ℓ} → {B : Group c ℓ} →
  (f : A ⟶ Group.setoid B) → (h : group A -Group→ B) →
  ((z : Setoid.Carrier A) → Group._≈_ B (_-Group→_.⟦_⟧ h [ gen z ]) (f ⟨$⟩ z)) →
  (w : Word A) → Group._≈_ B (_-Group→_.⟦_⟧ h w) (_-Group→_.⟦_⟧ ([_]* {B = B} f) w)
lift-uniq f h eq [] = _-Group→_.ε-homo h
lift-uniq {A = A} {B = B} f h eq (x ∷ xs) =
    begin
      ⟦ x ∷ xs ⟧
    ≈⟨ refl₂ ⟩
      ⟦ [ x ] ∙₁ xs ⟧
    ≈⟨ ∙-homo _ _ ⟩
      ⟦ [ x ] ⟧ ∙₂ ⟦ xs ⟧
    ≈⟨ ∙₂-cong (lift-uniq-1 x) (lift-uniq f h eq xs) ⟩
      f⟦ [ x ] ⟧ ∙₂ f⟦ xs ⟧
    ≈⟨ sym₂ (∙₂-homo [ x ] xs) ⟩
      f⟦ x ∷ xs ⟧
    ∎
  where
     open Group B renaming (_∙_ to _∙₂_; _≈_ to _≈₂_; ∙-cong to ∙₂-cong;
          refl to refl₂; sym to sym₂; assoc to assoc₂; trans to trans₂;
          ε to ε₂; inverse to inverse₂; identity to identity₂)
     open Group (group A) using () renaming (_∙_ to _∙₁_; _≈_ to _≈₁_; _⁻¹ to _⁻¹₁)
     open EqR (Group.setoid B)
     open _-Group→_ h
     open _-Group→_ ([_]* {B = B} f) using () renaming
       (⟦_⟧ to f⟦_⟧; ∙-homo to ∙₂-homo; ⟦⟧-cong to f⟦⟧-cong; ⁻¹-homo to ⁻¹₂-homo)
 
     lift-uniq-gen : ∀ x →  ⟦ [ gen x ] ⟧ ≈₂ f⟦ [ gen x ] ⟧
     lift-uniq-gen y = trans₂ (eq y) (sym₂ (proj₂ identity₂ (f ⟨$⟩ y)))
  
     lift-uniq-1 : ∀ x →  ⟦ [ x ] ⟧ ≈₂ f⟦ [ x ] ⟧
     lift-uniq-1 (gen y) = lift-uniq-gen y
     lift-uniq-1 (gen-inv y) = begin 
       ⟦ [ gen y ] ⁻¹₁ ⟧ 
         ≈⟨ ⁻¹-homo _ ⟩
       ⟦ [ gen y ] ⟧ ⁻¹ 
         ≈⟨ ⁻¹-cong (lift-uniq-gen y) ⟩
       f⟦ [ gen y ] ⟧ ⁻¹ 
         ≈⟨ sym₂ (⁻¹₂-homo [ gen y ]) ⟩
       f⟦ [ gen y ] ⁻¹₁ ⟧ 
       ∎

  