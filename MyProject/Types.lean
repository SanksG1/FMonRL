/-
  MyProject/MDP/Types.lean
  Minimal discounted finite MDP types (finite S, finite A s), with plain-ℝ transitions.
-/
import Mathlib
open scoped BigOperators

universe u v

namespace MDP

/-- A discounted finite MDP. -/
structure Model where
  -- State space (finite, decidable equality)
  S : Type u
  [decS : DecidableEq S]
  [finS : Fintype S]

  -- Action space is state-dependent and finite for each state
  A    : S → Type v
  decA : ∀ s : S, DecidableEq (A s)
  finA : ∀ s : S, Fintype (A s)
  nonemptyA : ∀ s : S, Nonempty (A s)        -- needed for `Finset.sup'` on actions

  -- Rewards and transition kernel (discrete probabilities into S)
  r    : ∀ s : S, (A s) → ℝ
  r_bdd : ∃ C : ℝ, ∀ s a, |r s a| ≤ C        -- convenient for boundedness preservation
  P    : ∀ s : S, (A s) → S → ℝ

  -- Discount factor γ with 0 ≤ γ < 1
  γ         : ℝ
  γ_nonneg  : 0 ≤ γ
  γ_lt_one  : γ < 1

  -- Probability axioms
  P_nonneg  : ∀ s a s', 0 ≤ P s a s'
  P_sum_one : ∀ s a, ∑ s' : S, P s a s' = 1

/-- Expected value of `V` from `(s,a)` under `P`. -/
def EV (M : Model) (V : M.S → ℝ) (s : M.S) (a : M.A s) : ℝ := by
  classical
  -- bring finite/decidable instances for the state index into scope
  letI := M.finS
  letI := M.decS
  exact ∑ s' : M.S, M.P s a s' * V s'

/-- A simple boundedness predicate for value functions. -/
def Bdd (M : Model) (V : M.S → ℝ) : Prop :=
  ∃ C : ℝ, ∀ s : M.S, |V s| ≤ C

/-- If `V` is bounded then `EV V` is uniformly bounded in `(s,a)`. -/
lemma EV_bdd_of_bdd {M : Model} (V : M.S → ℝ) (hV : Bdd M V) :
    ∃ C : ℝ, ∀ (s : M.S) (a : M.A s), |EV M V s a| ≤ C := by
  -- Triangle inequality + nonnegativity of P + `∑ P = 1` + boundedness of `V`.
  -- We'll fill in the finite-sum details later.
  sorry

end MDP
