import Mathlib.Data.Set.Basic
import Mathlib.Data.Bool.Basic

universe u

namespace PropLogic

/-!
v ⊨ φ iff eval v φ = true
φ is valid iff ¬φ is unsatisfiable
φ ≡ ψ iff
  (φ ∧ ¬ψ) ∨ (ψ ∧ ¬φ)
is unsatisfiable
-/


inductive Formula (PropVar : Type u) where
| atom : PropVar → Formula PropVar
| neg  : Formula PropVar → Formula PropVar
| or   : Formula PropVar → Formula PropVar → Formula PropVar
| and  : Formula PropVar → Formula PropVar → Formula PropVar
| imp  : Formula PropVar → Formula PropVar → Formula PropVar
deriving DecidableEq

abbrev Valuation (PropVar : Type u) :=
  PropVar → Bool


def eval {PropVar : Type u}
    (v : Valuation PropVar) :
    Formula PropVar → Bool
| .atom p    => v p
| .neg φ     => !(eval v φ)
| .or φ ψ    => eval v φ || eval v ψ
| .and φ ψ   => eval v φ && eval v ψ
| .imp φ ψ   => (! eval v φ) || eval v ψ


def Satisfies {PropVar : Type u}
    (v : Valuation PropVar) :
    Formula PropVar → Prop
| .atom p    => v p = true
| .neg φ     => ¬ Satisfies v φ
| .or φ ψ    => Satisfies v φ ∨ Satisfies v ψ
| .and φ ψ   => Satisfies v φ ∧ Satisfies v ψ
| .imp φ ψ   => Satisfies v φ → Satisfies v ψ


notation:50 v " ⊨ " φ => Satisfies v φ

theorem satisfies_iff_eval_true
    {PropVar : Type u}
    (v : Valuation PropVar)
    (φ : Formula PropVar) :
    (v ⊨ φ) ↔ eval v φ = true := by
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


def Models {PropVar : Type u}
    (φ : Formula PropVar) :
    Set (Valuation PropVar) :=
  {v | v ⊨ φ}


def Equivalent {PropVar : Type u}
    (φ ψ : Formula PropVar) : Prop :=
  Models φ = Models ψ

notation:50 φ " ≡ " ψ => Equivalent φ ψ


def Satisfiable {PropVar : Type u}
    (φ : Formula PropVar) : Prop :=
  ∃ v, v ⊨ φ

def Unsatisfiable {PropVar : Type u}
    (φ : Formula PropVar) : Prop :=
  ¬ Satisfiable φ

def Valid {PropVar : Type u}
    (φ : Formula PropVar) : Prop :=
  ∀ v, v ⊨ φ


lemma satisfies_not_neg
    {PropVar : Type u}
    (v : Valuation PropVar)
    (φ : Formula PropVar) :
    (v ⊨ φ) → ¬ (v ⊨ Formula.neg φ) := by
  intro hφ hneg
  exact hneg hφ

lemma not_both_formula_and_negation
    {PropVar : Type u}
    (v : Valuation PropVar)
    (φ : Formula PropVar) :
    ¬ ((v ⊨ φ) ∧ (v ⊨ Formula.neg φ)) := by
  intro h
  exact h.2 h.1

theorem valid_iff_neg_unsatisfiable
    {PropVar : Type u}
    (φ : Formula PropVar) :
    Valid φ ↔ Unsatisfiable (Formula.neg φ) := by
  constructor

  · intro hvalid
    intro hsat

    rcases hsat with ⟨v, hv⟩

    have hφ : v ⊨ φ := hvalid v

    exact hv hφ

  · intro hunsat
    intro v

    by_contra hφ

    apply hunsat

    exact ⟨v, hφ⟩


def Diff {PropVar : Type u}
    (φ ψ : Formula PropVar) :
    Formula PropVar :=
  Formula.or
    (Formula.and φ (Formula.neg ψ))
    (Formula.and ψ (Formula.neg φ))


theorem equivalent_iff_diff_unsat
    {PropVar : Type u}
    (φ ψ : Formula PropVar) :
    Equivalent φ ψ ↔ Unsatisfiable (Diff φ ψ) := by
  constructor
  · intro heq
    intro hsat
    rcases hsat with ⟨v, hv⟩
    rcases hv with
      (⟨hφ, hnψ⟩ | ⟨hψ, hnφ⟩)
    ·
      have hvmem : v ∈ Models φ := hφ
      have hψ : v ∈ Models ψ := by
        rw [← heq]
        exact hvmem
      exact hnψ hψ
    ·
      have hvmem : v ∈ Models ψ := hψ
      have hφ : v ∈ Models φ := by
        rw [heq]
        exact hvmem
      exact hnφ hφ
  · intro hunsat
    ext v
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


theorem equivalent_iff_satisfies
    {PropVar : Type u}
    (φ ψ : Formula PropVar) :
    Equivalent φ ψ ↔ ∀ v, (v ⊨ φ) ↔ (v ⊨ ψ) := by
  constructor
  · intro heq
    intro v
    change v ∈ Models φ ↔ v ∈ Models ψ
    rw [heq]
  · intro h
    ext v
    exact h v


end PropLogic
