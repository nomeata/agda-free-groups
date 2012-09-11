module GroupHom where

open import Algebra.Morphism
open import Algebra
open import Level
open import Relation.Binary
import Algebra.Props.Group as GroupP
import Relation.Binary.EqReasoning as EqR
open import Data.Product

record _-Group→_ {r₁ r₂ r₃ r₄}
                (From : Group r₁ r₂) (To : Group r₃ r₄) :
                Set (r₁ ⊔ r₂ ⊔ r₃ ⊔ r₄) where
  private
    module F = Group From
    module T = Group To
  open Definitions F.Carrier T.Carrier T._≈_

  field
    ⟦_⟧     : Morphism
    ⟦⟧-cong : ⟦_⟧ Preserves F._≈_ ⟶ T._≈_
    ∙-homo  : Homomorphic₂ ⟦_⟧ F._∙_ T._∙_

  open EqR T.setoid

  ε-homo :  Homomorphic₀ ⟦_⟧ F.ε T.ε
  ε-homo = GroupP.left-identity-unique To ⟦ F.ε ⟧ ⟦ F.ε ⟧ (begin
      T._∙_ ⟦ F.ε ⟧ ⟦ F.ε ⟧ ≈⟨ T.sym (∙-homo _ _) ⟩
      ⟦ F._∙_ _ _ ⟧         ≈⟨ ⟦⟧-cong (proj₁ F.identity _) ⟩
      ⟦ F.ε ⟧                ∎)

  ⁻¹-homo : Homomorphic₁ ⟦_⟧ F._⁻¹ T._⁻¹
  ⁻¹-homo x = GroupP.left-inverse-unique To ⟦ F._⁻¹ x  ⟧ ⟦ x ⟧ (begin
    T._∙_ ⟦ F._⁻¹ x ⟧ ⟦ x ⟧
      ≈⟨ T.sym (∙-homo _ _) ⟩
    ⟦ F._∙_ (F._⁻¹ x) x ⟧
      ≈⟨ ⟦⟧-cong (proj₁ F.inverse _) ⟩
    ⟦ F.ε ⟧
      ≈⟨ ε-homo ⟩
    T.ε
    ∎)
