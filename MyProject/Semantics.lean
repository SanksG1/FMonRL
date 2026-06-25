import Mathlib.Data.Set.Basic
import Mathlib.Data.Bool.Basic

universe u

namespace PropLogic

/-
  Syntax of formulas.
  This corresponds to the abstract formulas
  used in the semantics section.
-/

inductive Formula (PropVar : Type u) where
| atom : PropVar → Formula PropVar
| neg  : Formula PropVar → Formula PropVar
| or   : Formula PropVar → Formula PropVar → Formula PropVar
| and  : Formula PropVar → Formula PropVar → Formula PropVar
| imp  : Formula PropVar → Formula PropVar → Formula PropVar
deriving DecidableEq

/-
  Assignments / valuations.
-/

abbrev Valuation (PropVar : Type u) :=
  PropVar → Bool

/-
  Value of a formula under an assignment.
  This is Definition 3 from the paper.
-/

def eval {PropVar : Type u}
    (v : Valuation PropVar) :
    Formula PropVar → Bool
| .atom p    => v p
| .neg φ     => !(eval v φ)
| .or φ ψ    => eval v φ || eval v ψ
| .and φ ψ   => eval v φ && eval v ψ
| .imp φ ψ   => (! eval v φ) || eval v ψ

/-
  Satisfaction relation.
  This mirrors Definition 2.
-/

def Satisfies {PropVar : Type u}
    (v : Valuation PropVar) :
    Formula PropVar → Prop
| .atom p    => v p = true
| .neg φ     => ¬ Satisfies v φ
| .or φ ψ    => Satisfies v φ ∨ Satisfies v ψ
| .and φ ψ   => Satisfies v φ ∧ Satisfies v ψ
| .imp φ ψ   => Satisfies v φ → Satisfies v ψ

/-
  Lemma:
  v ⊨ φ iff v[φ] = T
-/

theorem satisfies_iff_eval_true
    {PropVar : Type u}
    (v : Valuation PropVar)
    (φ : Formula PropVar) :
    Satisfies v φ ↔ eval v φ = true := by
  induction φ with
  | atom p =>
      simp [Satisfies, eval]
  | neg φ ih =>
      simp [Satisfies, eval, ih]
  | or φ ψ ihφ ihψ =>
      simp [Satisfies, eval, ihφ, ihψ]
  | and φ ψ ihφ ihψ =>
      simp [Satisfies, eval, ihφ, ihψ]
  | imp φ ψ ihφ ihψ =>
      by_cases hφ : eval v φ = true
      · simp [Satisfies, eval, ihφ, ihψ, hφ]
      · simp [Satisfies, eval, ihφ, ihψ, hφ]

/-
  Models.
-/

def Models {PropVar : Type u}
    (φ : Formula PropVar) :
    Set (Valuation PropVar) :=
  {v | Satisfies v φ}

/-
  Semantic equivalence.
-/

def Equivalent {PropVar : Type u}
    (φ ψ : Formula PropVar) : Prop :=
  ∀ v, Satisfies v φ ↔ Satisfies v ψ

/-
  Satisfiable / Unsatisfiable / Valid.
-/

def Satisfiable {PropVar : Type u}
    (φ : Formula PropVar) : Prop :=
  ∃ v, Satisfies v φ

def Unsatisfiable {PropVar : Type u}
    (φ : Formula PropVar) : Prop :=
  ¬ Satisfiable φ

def Valid {PropVar : Type u}
    (φ : Formula PropVar) : Prop :=
  ∀ v, Satisfies v φ

/-
  Valid iff negation is unsatisfiable.
-/

theorem valid_iff_neg_unsatisfiable
    {PropVar : Type u}
    (φ : Formula PropVar) :
    Valid φ ↔ Unsatisfiable (.neg φ) := by
  constructor
  · intro hvalid hsat
    rcases hsat with ⟨v, hv⟩
    exact hv (hvalid v)
  · intro hunsat v
    by_contra hv
    apply hunsat
    refine ⟨v, ?_⟩
    exact hv

/-
  Formula expressing disagreement.
-/

def Diff {PropVar : Type u}
    (φ ψ : Formula PropVar) : Formula PropVar :=
  Formula.or
    (Formula.and φ (Formula.neg ψ))
    (Formula.and ψ (Formula.neg φ))

/-
  Equivalent iff disagreement formula is unsatisfiable.
-/

theorem equivalent_iff_diff_unsat
    {PropVar : Type u}
    (φ ψ : Formula PropVar) :
    Equivalent φ ψ ↔ Unsatisfiable (Diff φ ψ) := by
  constructor
  · intro heq hsat
    rcases hsat with ⟨v, hv⟩
    rcases hv with
      (⟨hφ, hnψ⟩ | ⟨hψ, hnφ⟩)
    · exact hnψ ((heq v).mp hφ)
    · exact hnφ ((heq v).mpr hψ)
  · intro hunsat v
    constructor
    · intro hφ
      by_contra hψ
      apply hunsat
      refine ⟨v, ?_⟩
      left
      exact ⟨hφ, hψ⟩
    · intro hψ
      by_contra hφ
      apply hunsat
      refine ⟨v, ?_⟩
      right
      exact ⟨hψ, hφ⟩

end PropLogic
