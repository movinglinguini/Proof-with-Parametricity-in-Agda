open import Data.Bool.Base using (Bool; true; false; T; not)
open import Data.String using (String; _≟_)
-- open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

open import SystemF

module Parametricity where 
  -- Logical Equivalence... sort of
  data _∼⟦_⟧_ : Expr → Type → Expr → Set where
    expr : ∀ { e₁ e₂ v₁ v₂ τ }
      → e₁ ⟶* v₁ → e₂ ⟶* v₂ → v₁ ∼⟦ τ ⟧ v₂ 
      ------------------------------------------------------------
      → e₁ ∼⟦ τ ⟧ e₂

    tylam : ∀ { v₁ v₂ τ R α σ σ' }
      → (v₁ [ σ ]) ∼⟦ [ R := α ]t τ ⟧ (v₂ [ σ' ])
      --------------------------------
      → v₁ ∼⟦ all[ α ]⇒ τ ⟧ v₂

    tylam-inv : ∀ { v₁ v₂ τ R α σ σ' }
      → v₁ ∼⟦ all[ α ]⇒ τ ⟧ v₂  
      --------------------------------
      → (v₁ [ σ ]) ∼⟦ [ R := α ]t τ ⟧ (v₂ [ σ' ])

    lam : ∀ { f₁ f₂ τ₁ τ₂ v₁ v₂ }
      → v₁ ∼⟦ τ₁ ⟧ v₂ → (f₁ ∙ v₁) ∼⟦ τ₂ ⟧ (f₂ ∙ v₂)
      ---------------------------------
      → f₁ ∼⟦ τ₁ ⇒ τ₂ ⟧ f₂

    lam-inv : ∀ { f₁ f₂ τ₁ τ₂ v₁ v₂ }
      → f₁ ∼⟦ τ₁ ⇒ τ₂ ⟧ f₂ → v₁ ∼⟦ τ₁ ⟧ v₂ 
      ----------------------
      → (f₁ ∙ v₁) ∼⟦ τ₂ ⟧ (f₂ ∙ v₂)

  postulate
    -- This is the paremtricity theorem. We don't prove it here. Theorem taken from Frank Pfenning's notes.
    parametricity : ∀ { τ M } → (∅ ⊢ M ⦂ τ) → M ∼⟦ τ ⟧ M
    
    -- These are for our demonstration. f is some expression with polymorphic type ∀α.α → α
    f : Expr
    f-type : ∀ { α } → ∅ ⊢ f ⦂ (all[ α ]⇒ ((` α) ⇒ (` α)))
    
    -- We'll need this for lemma 1
    -- If e1 and e2 are logically equivalent, one of the things we can conclude is that e1 steps to a value v1.
    expr/inv-1 : ∀ { e₁ e₂ τ v₁ }
      → e₁ ∼⟦ τ ⟧ e₂
      --------------------------
      → (e₁ ⟶* v₁)

    -- σ₀ : Type
    v₀~v₀ : ∀ { τ v₀ } → v₀ ∼⟦ τ ⟧ v₀

  id = Λ[ "α" ]⇒ (ƛ[ "x" ]⇒ ` "x")
  f-is-id : ∀ { α } → f ∼⟦ all[ α ]⇒ ((` α) ⇒ (` α)) ⟧ id
  f-is-id = tylam lemma-2
    where
      -- Lemma 1
      lemma-1 : ∀ { v σ } → ((f [ σ ] ) ∙ v) ⟶* v
      lemma-1 { v₀ } { σ₀ } = expr/inv-1 { (f [ σ₀ ]) ∙ v₀ } { (f [ σ₀ ]) ∙ v₀ } (lam-inv (tylam-inv (parametricity f-type)) v₀~v₀)
      
      -- For the theorem statement, we'll need to step through id ∙ v
      idv→v : ∀ { v σ } → ((id [ σ ]) ∙ v) ⟶* v
      idv→v { v } = step/trans (step/trans step/refl (app/1 tyapp/lam)) (app/lam vValue) 
        where
          postulate
            vValue : Value v
      
      -- -- step/trans (step/trans step/refl (app/1 tyapp/lam)) app/lam

      lemma-2 : ∀ { σ σ' τ α } → (f [ σ ]) ∼⟦ τ ⇒ τ ⟧ (id [ σ' ])
      lemma-2 { σ } { σ' } { τ } = lam v~v (expr lemma-1 idv→v v~v)
        where
          postulate
            v~v : ∀ { v v' } → v ∼⟦ τ ⟧ v'
              
    