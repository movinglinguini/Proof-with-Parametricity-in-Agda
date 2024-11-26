open import Data.Bool.Base using (Bool; true; false; T; not)

open import SystemF

module Parametricity where 
  -- Logical Equivalence
  Rel = Type → Type → Set

  data _∼[_]_ : Expr → Rel → Expr → Set₁ where
    tylam : ∀ { v₁ v₂ R σ σ' }
      → Value v₁ → Value v₂ → (R σ σ') → (v₁ [ σ ]) ∼[ R ] (v₂ [ σ' ])

  data _≈[_]_ : Expr → Rel → Expr → Set₁ where
    expr : ∀ { e₁ e₂ v₁ v₂ R }
      → Value v₁ → Value v₂ → e₁ ⟶* v₁ → e₂ ⟶* v₂ → v₁ ∼[ R ] v₂ 
      ------------------------------------------------------------
      → e₁ ≈[ R ] e₂
  