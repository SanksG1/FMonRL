import Mathlib
import MyProject.Types
open scoped BigOperators

namespace MDP
noncomputable section

/-- Q-value given a value function `V`. -/
def Q (M : Model) (V : M.S → ℝ) (s : M.S) (a : M.A s) : ℝ :=
  M.r s a + M.γ * EV M V s a

/-- Bellman optimality operator: `(T V)(s) = max_{a∈A(s)} Q(V)(s,a)`. -/
def bellman (M : Model) (V : M.S → ℝ) : M.S → ℝ :=
  fun s => by
    classical
    -- per-state action instances & state instances
    letI := M.decA s; letI := M.finA s
    letI := M.decS;  letI := M.finS
    -- Nonempty action set to use `sup'`
    have hne : (Finset.univ : Finset (M.A s)).Nonempty :=
      (M.nonemptyA s).elim (fun a => ⟨a, by simp⟩)
    exact Finset.sup' (Finset.univ : Finset (M.A s)) hne (fun a => Q M V s a)

/-!
  Helpers to talk about sup-norms *without* putting `Finset.univ` in lemma types.
  We define the "sup over states" inside a `by` block so we can bring instances
  into scope locally. If `S` is empty, we return `0` (harmless for our inequalities).
-/

/-- `supS M f = sup_{s∈S} f s` (returns `0` if `S` is empty). -/
def supS (M : Model) (f : M.S → ℝ) : ℝ := by
  classical
  letI := M.decS; letI := M.finS
  by_cases hne : (Finset.univ : Finset M.S).Nonempty
  · exact Finset.sup' (Finset.univ : Finset M.S) hne f
  · exact 0

/-- `supDiff M V W = sup_s |V s - W s|`. -/
def supDiff (M : Model) (V W : M.S → ℝ) : ℝ :=
  supS M (fun s => |V s - W s|)

/-- `supBellDiff M V W = sup_s |(T V) s - (T W) s|`. -/
def supBellDiff (M : Model) (V W : M.S → ℝ) : ℝ :=
  supS M (fun s => |bellman M V s - bellman M W s|)

/-! ### Lipschitz building blocks (declared; proofs later) -/
/-- For finite `S`, the metric `dist` on functions coincides with our `supDiff`. -/
lemma dist_eq_supDiff
    (M : Model) (V W : M.S → ℝ)
    [Fintype M.S] [DecidableEq M.S] :
  dist V W = supDiff M V W := by
  -- Bring the concrete instances (so you can rewrite/compute if needed)
  classical
  haveI := M.finS
  haveI := M.decS
  -- Unfold `dist` on Pi types (sup metric) and `supDiff/supS`; routine bookkeeping.
  sorry

/-- Repackage `bellman_lipschitz_sup` as a Lipschitz-with statement on `dist`. -/
lemma bellman_lipschitzWith
    (M : Model) [Fintype M.S] [DecidableEq M.S] :
  LipschitzWith ⟨M.γ, M.γ_nonneg⟩ (bellman M) := by
  classical
  -- One clean way is: rewrite `dist` to your sup-norm (via a helper
  -- `dist_eq_supDiff`) and then use `bellman_lipschitz_sup`.
  -- We keep it stubbed to focus on wiring.
  sorry

/-- Max over a finite **nonempty** index set is 1-Lipschitz (in `ℝ`). -/
lemma max_lipschitz_finset
  {ι : Type} [DecidableEq ι] [Fintype ι] [Nonempty ι]
  (f g : ι → ℝ) :
  |(Finset.sup' (Finset.univ) (Finset.univ_nonempty) f)
   - (Finset.sup' (Finset.univ) (Finset.univ_nonempty) g)|
  ≤ Finset.sup' (Finset.univ) (Finset.univ_nonempty) (fun i => |f i - g i|) := by
  -- Standard argument: both sups are ≤ sup of pointwise absolute diff,
  -- use triangle inequality and choice of maximizers. We’ll fill it later.
  sorry

/-- Expectation under a prob. vector is 1-Lipschitz in the sup norm (finite `S`). -/
lemma EV_lipschitz_sup (M : Model) (V W : M.S → ℝ) (s : M.S) (a : M.A s) :
  |EV M V s a - EV M W s a| ≤ supDiff M V W := by
  classical
  letI := M.decS; letI := M.finS
  -- Expand sum, triangle inequality, use `P_nonneg` and `P_sum_one`, then
  -- bound by the sup over `|V - W|`.
  sorry

/-- Bellman is γ-Lipschitz w.r.t. the sup norm on `S → ℝ`. -/
lemma bellman_lipschitz_sup (M : Model) (V W : M.S → ℝ) :
  supBellDiff M V W ≤ M.γ * supDiff M V W := by
  classical
  letI := M.decS; letI := M.finS
  -- For each `s`, use `max_lipschitz_finset` on actions (with `[Nonempty (A s)]`
  -- coming from `M.nonemptyA s`) and then `EV_lipschitz_sup`, pulling out `γ`.
  -- Finally, take sup via `supS`.
  sorry

/-- Bellman preserves boundedness if rewards are bounded. -/
lemma bellman_bdd_of_bdd (M : Model) (V : M.S → ℝ)
  (hV : Bdd M V) : Bdd M (bellman M V) := by
  -- Use `M.r_bdd`, `EV_bdd_of_bdd`, and finiteness of `A s` to bound the `sup'`.
  sorry

end
end MDP
