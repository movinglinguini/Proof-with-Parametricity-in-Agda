open import Data.String using (String; _≟_)
open import Relation.Nullary.Decidable using (yes; no)

module SystemF where
  Id : Set
  Id = String

  -- Types
  data Type : Set where
    -- Base Type : bool
    Bool : Type
    -- Type variable
    `_ : Id → Type
    -- Function type
    _⇒_ : Type → Type → Type
    -- Polymorphic type
    all[_]⇒_ : Id → Type → Type

  -- Expressions
  data Expr : Set where
    -- Boolean expressions
    true : Expr
    false : Expr
    -- Variable
    `_ : Id → Expr
    -- Function expression
    ƛ[_]⇒_ : Id → Expr → Expr
    -- Polymorphic
    Λ[_]⇒_ : Id → Expr → Expr
    -- Poly-app
    _[_] : Expr → Type → Expr
    -- Application
    _∙_ : Expr → Expr → Expr

  -- Expression substitution
  [_:=_]e_ : Expr → Id → Expr → Expr
  [ N := x ]e true = true 
  [ N := x ]e false = false
  [ N := x ]e (` y) with x ≟ y
  ... | yes _ = N
  ... | no _ = ` y
  [ N := x ]e (ƛ[ y ]⇒ M) with x ≟ y
  ... | yes _ = ƛ[ y ]⇒ M
  ... | no _ = ƛ[ y ]⇒ ([ N := x ]e M)
  [ N := x ]e (M₁ ∙ M₂) = ([ N := x ]e M₁) ∙ ([ N := x ]e M₂)
  [ N := x ]e (Λ[ y ]⇒ M) = Λ[ y ]⇒ ([ N := x ]e M)
  [ N := x ]e (M [ α ]) = ([ N := x ]e M)[ α ]

  -- Substitution rules for types
  [_:=_]t_ : Type → Id → Type → Type
  [ U := α ]t Bool = Bool 
  [ U := α ]t (` x) with α ≟ x
  ... | yes _ = U
  ... | no _ = ` x
  [ U := α ]t (T₁ ⇒ T₂) = ([ U := α ]t T₁) ⇒ ([ U := α ]t T₂)
  [ U := α ]t (all[ x ]⇒ T) with α ≟ x
  ... | yes _ = all[ x ]⇒ T
  ... | no _ = all[ x ]⇒ ([ U := α ]t T)

  -- Value judgements
  data Value : Expr → Set where
    tt : Value true

    ff : Value false

    exlam : ∀ { x e } → Value (ƛ[ x ]⇒ e)

    tylam : ∀ { α e } → Value (Λ[ α ]⇒ e)

  -- Step Rules
  data _⟶_ : Expr → Expr → Set where
    app/1 : ∀ {M M' N : Expr}
      → M ⟶ M'
        -----------------
      → (M ∙ N) ⟶ (M' ∙ N)

    app/2 : ∀ {V M M'}
      → Value V  → M ⟶ M'
        -----------------
      → (V ∙ M) ⟶ (V ∙ M')

    app/lam : ∀ {x N V}
      → Value V
        ------------------------------
      → ((ƛ[ x ]⇒ N) ∙ V) ⟶ ([ V := x ]e N)

    tyapp/lam : ∀ { α τ M }
      → ((Λ[ α ]⇒ M)[ τ ]) ⟶ M

  -- Reflexive, transitive closure of step
  data _⟶*_ : Expr → Expr → Set where
    step/refl : ∀ { M }
      ------------------
      → M ⟶* M
    
    step/trans : ∀ { L M N }
      → L ⟶* M → M ⟶ N
      -------------------
      → L ⟶* N

  -- Typing Context
  data Ctxt : Set where
    ∅ : Ctxt
    _,_⦂_ : Ctxt → Id → Type → Ctxt

  -- Typing Rules
  data _⊢_⦂_ : Ctxt → Expr → Type → Set where
    ty/true : ∀ { Γ }
      -------------
      → Γ ⊢ true ⦂ Bool

    ty/false : ∀ { Γ }
      -------------
      → Γ ⊢ false ⦂ Bool

  