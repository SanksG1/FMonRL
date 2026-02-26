/-
  MDP/ValueIteration.lean

  A from-scratch, minimal, sorry-based skeleton for formalizing
  value-iteration convergence via contraction mapping.

  Everything is organized top-down with dependencies annotated.
  You can fill in proofs incrementally without wrestling imports.
-/

import Mathlib

open scoped BigOperators
open Filter

-- A finite-state, finite-nonempty-action MDP model.
structure MDP where
  S : Type*
  decS : DecidableEq S
  finS : Fintype S
  S_nonempty : Nonempty S
  A : Type*
  decA : DecidableEq A
  Aset : S → Finset A
  Aset_nonempty : ∀ s, (Aset s).Nonempty
  P : S → A → PMF S
  r : S → A → ℝ
  γ : ℝ
  γ_nonneg : 0 ≤ γ
  γ_lt_one : γ < 1

namespace MDP

/-! ###############################################################
    1) ABSTRACT LAYER: Contraction → fixed point + convergence + rate
    ############################################################### -/

section Abstract

-- Abstract setting for Banach/Picard.
-- Used by: all final MDP theorems via specialization with X := S → ℝ.
-- Depends on: only core metric/complete space typeclasses.

variable {X : Type*} [PseudoMetricSpace X] [CompleteSpace X]

/-- Contractive map with constant `γ ∈ [0,1)`. -/
structure IsContraction (T : X → X) (γ : ℝ) : Prop where
  (nonneg : 0 ≤ γ)
  (lt_one : γ < 1)
  (lipschitz : ∀ x y, dist (T x) (T y) ≤ γ * dist x y)

-- Used by: all abstract lemmas below, then specialized for Bellman T.
/-- Picard iteration: `x_{n+1} = T (x_n)` starting from `x0`. -/
def picard (T : X → X) (x0 : X) : ℕ → X
  | 0       => x0
  | (n + 1) => T (picard T x0 n)

-- Depends on: IsContraction; Used by: `contraction_has_unique_fixedPoint`, others.
/-- Banach fixed-point theorem (existence & uniqueness of fixed point). -/
theorem contraction_has_unique_fixedPoint
  {T : X → X} {γ : ℝ} (h : IsContraction T γ) :
∃! xStar, T xStar = xStar := by
  -- Proof sketch you will implement:
  -- 1) Show Picard is Cauchy using geometric bound.
  -- 2) Use completeness for existence of limit.
  -- 3) Lipschitz ⇒ continuity ⇒ limit is fixed point.
  -- 4) Uniqueness via `dist y xStar ≤ γ dist y xStar`.
  sorry

-- Depends on: `contraction_has_unique_fixedPoint`; Used by: final convergence theorem.
/-- Picard iterates converge to the unique fixed point. -/
theorem picard_converges_to_fixedPoint
  {T : X → X} {γ : ℝ} (h : IsContraction T γ) (x0 : X) :
  ∃ xStar, T xStar = xStar ∧ Tendsto (fun n => picard T x0 n) atTop (nhds xStar) := by
  sorry

-- Depends on: `contraction_has_unique_fixedPoint`; Used by: final rate bound.
/-- Geometric error bound: `dist (x_n, xStar) ≤ γ^n * C` (e.g. `C = dist x0 xStar`). -/
theorem picard_error_bound
  {T : X → X} {γ : ℝ} (h : IsContraction T γ) (x0 : X) :
  let xStar := Classical.choose
    (ExistsUnique.exists (contraction_has_unique_fixedPoint (X := X) h))
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n, dist (picard T x0 n) xStar ≤ (γ ^ n) * C := by
  sorry

end Abstract


/-! ###############################################################
    2) MDP MODEL: finite MDP, expectation, Bellman operator
    ############################################################### -/

section Model
-- Provide instances extracted from the structure fields (so `Finset.univ` works).
instance instDecidableEqS (M : MDP) : DecidableEq M.S := M.decS
instance instFintypeS     (M : MDP) : Fintype     M.S := M.finS
instance instDecidableEqA (M : MDP) : DecidableEq M.A := M.decA

variable (M : MDP)
local notation "S" => M.S
local notation "A" => M.A

-- Used by: Bellman operator and Lipschitz lemmas.
/-- Finite-sum expectation under a `PMF` for a value function `V`. -/
def expVal (V : S → ℝ) (p : PMF S) : ℝ :=
  ∑ s, (p s).toReal * V s

-- Depends on: `expVal`, `Aset_nonempty`; Used by: contraction lemma.
/-- Bellman optimality operator on values `V : S → ℝ`. -/
def Topt (V : S → ℝ) : S → ℝ :=
  fun s =>
    (M.Aset s).sup' (M.Aset_nonempty s)
      (fun a => M.r s a + M.γ * expVal M V (M.P s a))

end Model


/-! ###############################################################
    3) METRIC/INEQUALITY LEMMAS (MDP plumbing)
    ############################################################### -/

section LipschitzBits

variable (M : MDP)
local notation "S" => M.S

-- Helper: `univ` is nonempty because `S` is nonempty.
private lemma univ_nonempty_S : (Finset.univ : Finset S).Nonempty := by
  classical
  rcases M.S_nonempty with ⟨s0⟩
  exact ⟨s0, by simp⟩

/-- Expectation is 1-Lipschitz in the sup (∞) metric:
    `|E_p[V] - E_p[W]| ≤ sup_s |V s - W s|`. -/
lemma expVal_diff_le_sup (V W : S → ℝ) (p : PMF S) :
  |expVal M V p - expVal M W p|
    ≤ (Finset.univ.sup' (univ_nonempty_S M) (fun s : S => |V s - W s|)) := by
  sorry

/-- Max over a finite set is 1-Lipschitz under sup-metric:
    `|sup_i x_i - sup_i y_i| ≤ sup_i |x_i - y_i|`. -/
lemma sup_finset_1Lipschitz
  {ι : Type*} [Fintype ι] [DecidableEq ι] [hι : Nonempty ι]
  (x y : ι → ℝ) :
  |(Finset.univ.sup' (by classical exact ⟨Classical.choice hι, by simp⟩) (fun i => x i))
    - (Finset.univ.sup' (by classical exact ⟨Classical.choice hι, by simp⟩) (fun i => y i))|
    ≤ Finset.univ.sup'
        (by classical exact ⟨Classical.choice hι, by simp⟩)
        (fun i => |x i - y i|) := by
  sorry

/-- For finite `S`, the `Pi` metric equals the sup of pointwise abs:
    `dist V W = sup_s |V s - W s|`. -/
lemma dist_eq_sup (V W : S → ℝ) :
  dist V W
    = (Finset.univ.sup' (univ_nonempty_S M) (fun s : S => |V s - W s|)) := by
  sorry

end LipschitzBits



/-! ###############################################################
    4) BELLMan OPERATOR IS A γ-CONTRACTION
    ############################################################### -/

section Contraction

variable (M : MDP)
local notation "S" => M.S

-- Depends on: `expVal_diff_le_sup`, `sup_finset_1Lipschitz`, `dist_eq_sup`.
-- Used by: the three final value-iteration theorems.
/-- The Bellman optimality operator is a contraction with constant `γ`. -/
theorem Topt_is_contraction :
  IsContraction (X := (S → ℝ)) (T := Topt M) (γ := M.γ) := by
  /- Outline to fill:
     1) Fix `V W` and a state `s`.
     2) Define `x_a := r s a + γ * E[V]`, `y_a := r s a + γ * E[W]`.
     3) `| (sup_a x_a) - (sup_a y_a) | ≤ sup_a |x_a - y_a|` (sup 1-Lip).
     4) `|x_a - y_a| = γ * |E[V]-E[W]| ≤ γ * sup_s |V-W|` (exp 1-Lip).
     5) Take sup over `s` and rewrite both sides as `dist` via `dist_eq_sup`.
  -/
  sorry

end Contraction


/-! ###############################################################
    5) VALUE ITERATION: existence, convergence, geometric rate
    ############################################################### -/

section ValueIteration

variable (M : MDP)
local notation "S" => M.S

-- Used by: final theorems.
/-- Value-iteration sequence: `V_{n+1} := Topt V_n`. -/
def Viter (M : MDP) (V0 : M.S → ℝ) : ℕ → (M.S → ℝ)
  | 0       => V0
  | (n + 1) => Topt M (Viter M V0 n)

-- Depends on: `Topt_is_contraction`; Used by: downstream results.
/-- Existence and uniqueness of the optimal value function `VStar`. -/
theorem exists_unique_Vstar :
  ∃! VStar : S → ℝ, Topt M VStar = VStar := by
  -- Apply abstract Banach with `X := S → ℝ` and `T := Topt M`.
  have h := Topt_is_contraction M
  simpa using
    (contraction_has_unique_fixedPoint
      (X := S → ℝ) (T := Topt M) (γ := M.γ) h)

-- Depends on: `Topt_is_contraction`, `exists_unique_Vstar`; Used by: rate bound.
/-- Value iteration converges to `VStar` from any start `V0`. -/
theorem valueIteration_converges (V0 : S → ℝ) :
  ∃ VStar : S → ℝ, Topt M VStar = VStar
    ∧ Tendsto (fun n => Viter M V0 n) atTop (nhds VStar) := by
  -- Specialize `picard_converges_to_fixedPoint` to `Topt` and `Viter`.
  -- Specialize Picard convergence to `T := Topt M` and `x0 := V0`.
  have h := Topt_is_contraction M
  rcases
    picard_converges_to_fixedPoint
      (X := S → ℝ) (T := Topt M) (γ := M.γ) h V0
    with ⟨VStar, hfix, hconv⟩
  refine ⟨VStar, hfix, ?_⟩
  -- Normalize `Viter` to `picard (T := Topt M)`.
  have eq_iter :
      (fun n => Viter M V0 n)
        = (fun n => picard (T := Topt M) V0 n) := by
    funext n;
    induction n with
    | zero => rfl
    | succ n ih => simp [Viter, picard, ih]
  simpa [eq_iter] using hconv

-- Depends on: `Topt_is_contraction`, `exists_unique_Vstar`; final theorem.
/-- Geometric error bound:
    `dist (V_n, VStar) ≤ γ^n * C` (take e.g. `C = dist (V0, VStar)`). -/
theorem valueIteration_error_bound (V0 : S → ℝ) :
  let VStar := Classical.choose
    (ExistsUnique.exists (exists_unique_Vstar M))
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n, dist (Viter M V0 n) VStar ≤ (M.γ ^ n) * C := by
  intro VStar
  have h := Topt_is_contraction M

  -- The `xStar` used by the abstract bound:
  let xStar :=
    Classical.choose
      (ExistsUnique.exists
        (contraction_has_unique_fixedPoint
          (X := S → ℝ) (T := Topt M) (γ := M.γ) h))
  have hx :
      Topt M xStar = xStar :=
    Classical.choose_spec
      (ExistsUnique.exists
        (contraction_has_unique_fixedPoint
          (X := S → ℝ) (T := Topt M) (γ := M.γ) h))

  -- The `VStar` in this statement:
  have hV :
      Topt M VStar = VStar :=
    Classical.choose_spec
      (ExistsUnique.exists (exists_unique_Vstar M))

  -- Uniqueness: the two fixed points coincide.
  have hEq : VStar = xStar :=
    (ExistsUnique.unique (exists_unique_Vstar M) hV (by simpa using hx)).symm

  -- Abstract geometric bound specialized to `Topt`.
  rcases
    (picard_error_bound (X := S → ℝ) (T := Topt M) (γ := M.γ) h V0)
      with ⟨C, hC0, hbound⟩
  have eq_iter :
      (fun n => Viter M V0 n)
        = (fun n => picard (T := Topt M) V0 n) := by
    funext n; induction n with
    | zero => rfl
    | succ n ih => simp [Viter, picard, ih]

  refine ⟨C, hC0, ?_⟩
  intro n
  -- Normalize: (i) `Viter` to `picard`; (ii) the chosen point to `xStar`;
  -- and then replace `xStar` by `VStar` using `hEq`.
  simpa [eq_iter, xStar, hEq, Viter, picard] using hbound n


end ValueIteration

end MDP
