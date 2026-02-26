import Mathlib.Data.NNReal.Defs
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Contracting
import MyProject.MDP

open scoped NNReal
open scoped BigOperators
open scoped Filter

open Filter

namespace MDP
namespace QLearning

section Model

variable (M : MDP)
local notation "S" => M.S
local notation "A" => M.A

instance instDecidableEqS : DecidableEq S := M.decS
instance instFintypeS     : Fintype S     := M.finS
instance instDecidableEqA : DecidableEq A := M.decA

/-- Dependent action type: actions available at a given state. -/
def Act (s : S) : Type := { a : A // a ∈ M.Aset s }

noncomputable instance instDecidableEqAct (s : S) : DecidableEq (Act (M := M) s) := by
  classical
  infer_instance

/--
State–action index type (dependent sigma):
an element is `⟨s, ⟨a, ha⟩⟩` meaning action `a` is valid at `s`.
-/
def SA : Type := Sigma (fun s : S => Act (M := M) s)
lemma SA_nonempty (M : MDP) : Nonempty (SA (M := M)) := by
  classical
  rcases M.S_nonempty with ⟨s0⟩
  rcases M.Aset_nonempty s0 with ⟨a0, ha0⟩
  exact ⟨⟨s0, ⟨a0, ha0⟩⟩⟩

noncomputable instance instDecidableEqSA : DecidableEq (SA (M := M)) := by
  classical
  -- `Sigma` decidable equality follows from decidable equality on components
  infer_instance

/-- Q-function space: tabular Q values on all valid (s,a). -/
abbrev QSpace : Type := (SA (M := M)) → ℝ

/-- Nonemptiness for abstract fixed-point theorems. -/
instance instNonemptyQSpace : Nonempty (QSpace (M := M)) := ⟨fun _ => 0⟩

/-- Helper: extract raw `s` and raw `a` from a sigma state-action. -/
def saState (sa : SA (M := M)) : S := sa.1
def saAct   (sa : SA (M := M)) : A := (sa.2 : Act (M := M) sa.1).val

/--
Given Q and a next state s', compute `max_{a'∈Aset s'}` Q(s',a').
We represent each valid action as `⟨a', ha'⟩ : Act s'` and then as sigma `⟨s', ⟨a', ha'⟩⟩ : SA`.
-/
def nextMax (Q : QSpace (M := M)) (s' : S) : ℝ :=
  (M.Aset s').sup' (M.Aset_nonempty s') (fun a' : A =>
    Q ⟨s', ⟨a', by
      -- membership proof needed
      -- `a' ∈ M.Aset s'` is exactly what `sup'` iterates over
      -- but we are in `fun a' => ...` so we need the proof from `a'` being in finset;
      -- easiest is to rewrite this function in a form that receives `a'` with membership.
      -- Keep skeleton:
      sorry⟩⟩
  )

/-
The above `nextMax` is *conceptually* correct but the membership proof plumbing is annoying
because `Finset.sup'` iterates over `A` and doesn’t pass membership evidence.
Two common fixes:
  (1) define `nextMax` using `Finset.sup'` on the *subtype* `{a // a ∈ Aset s'}`
  (2) define a helper `Act` finset and sup over it.

Below is the clean approach (2): build a finset of `Act s'`.
-/

/-- Finset of dependent actions at state s'. -/
def ActFinset (s : S) : Finset (Act (M := M) s) :=
  (M.Aset s).attach.map
    ⟨fun x => ⟨x.1, by simpa using x.2⟩, by
      intro x y h
      -- injective: underlying `A` is injective
      cases x with
      | mk x hx =>
        cases y with
        | mk y hy =>
          -- equality reduces to underlying A equality
          simpa using congrArg Subtype.val h⟩

lemma ActFinset_nonempty (s : S) : (ActFinset (M := M) s).Nonempty := by
  classical
  rcases M.Aset_nonempty s with ⟨a, ha⟩
  refine ⟨⟨a, ha⟩, ?_⟩
  -- show ⟨a,ha⟩ is in the mapped finset
  -- preimage in `attach`:
  have hx : (⟨a, ha⟩ : {x : A // x ∈ M.Aset s}) ∈ (M.Aset s).attach := by
    simpa using (Finset.mem_attach (s := M.Aset s) (⟨a, ha⟩ : {x : A // x ∈ M.Aset s}))
  -- now use `mem_map`:
  refine Finset.mem_map.2 ?_
  refine ⟨(⟨a, ha⟩ : {x : A // x ∈ M.Aset s}), hx, ?_⟩
  -- mapped value equals the target (proof fields are irrelevant)
  rfl

/-!
`Finset.univ` over `SA` is used later for sup-norm bounds.

We do **not** assume a global `Fintype A`. Instead, for each state `s` we
already have the finite set of admissible actions `M.Aset s : Finset A`. We
turn that into a finset of dependent actions `Act s`, and then form the finset
of all dependent state-action pairs using `Finset.sigma`.
-/

lemma mem_ActFinset (s : S) (a : Act (M := M) s) : a ∈ ActFinset (M := M) s := by
  classical
  -- Unfold and use `mem_map` with the obvious preimage in `attach`.
  rcases a with ⟨a, ha⟩
  have hx :
      (⟨a, ha⟩ : {x : A // x ∈ M.Aset s}) ∈ (M.Aset s).attach := by
    simpa using
      (Finset.mem_attach (s := M.Aset s)
        (⟨a, ha⟩ : {x : A // x ∈ M.Aset s}))
  refine Finset.mem_map.2 ?_
  refine ⟨(⟨a, ha⟩ : {x : A // x ∈ M.Aset s}), hx, ?_⟩
  rfl

noncomputable instance instFintypeSA : Fintype (SA (M := M)) := by
  classical
  -- Enumerate all `(s,a)` by `sigma` over `univ` and the per-state action finset.
  refine
    ⟨Finset.sigma (Finset.univ : Finset S) (fun s => ActFinset (M := M) s), ?_⟩
  intro sa
  rcases sa with ⟨s, a⟩
  -- Membership reduces to `s ∈ univ` and `a ∈ ActFinset s`.
  refine Finset.mem_sigma.2 ⟨Finset.mem_univ s, mem_ActFinset (M := M) s a⟩

/-- Now the max is painless. -/
def nextMax' (Q : QSpace (M := M)) (s' : S) : ℝ :=
  (ActFinset (M := M) s').sup' (ActFinset_nonempty (M := M) s')
    (fun a' : Act (M := M) s' => Q ⟨s', a'⟩)

/-- Q Bellman optimality operator: (TQ)(s,a) = r + γ * E[ max_a' Q(s',a') ]. -/
def Tq (Q : QSpace (M := M)) : QSpace (M := M) :=
  fun sa =>
    let s : S := sa.1
    let a : Act (M := M) s := sa.2
    M.r s a.1 + M.γ * expVal M (fun s' => nextMax' (M := M) Q s') (M.P s a.1)

end Model

section Contraction

variable (M : MDP)
local notation "S" => M.S

/-
Step 1 (analogue of your V-case):
Prove the “max over actions” is 1-Lipschitz w.r.t. sup norm on SA → ℝ.

You’ll likely want lemmas of the form:
  |sup f - sup g| ≤ sup |f-g|
over a nonempty finset (same pattern you used in `Topt_is_contraction`).
-/
lemma nextMax'_diff_le (Q R : QSpace (M := M)) (s : S) :
  |nextMax' (M := M) Q s - nextMax' (M := M) R s|
    ≤ (Finset.univ.sup' (by
        classical
        letI : Nonempty (SA (M := M)) := SA_nonempty (M := M)
        rcases (‹Nonempty (SA (M := M))›) with ⟨sa0⟩
        exact ⟨sa0, by simp⟩
      )
      (fun sa : SA (M := M) => |Q sa - R sa|)) := by
  classical
  sorry

/-
Step 2:
Bound the expectation difference using your existing lemma `expVal_diff_le_sup`,
but note we are applying expVal to a function on S:
  s' ↦ nextMax' Q s'
so we can reuse your V-space expectation lemma with V/W = these functions.
-/
lemma exp_nextMax_diff_le_sup (Q R : QSpace (M := M)) (p : PMF S) :
  |expVal M (fun s' => nextMax' (M := M) Q s') p
    - expVal M (fun s' => nextMax' (M := M) R s') p|
    ≤ (Finset.univ.sup' (by
        classical
        letI : Nonempty (SA (M := M)) := SA_nonempty (M := M)
        rcases (‹Nonempty (SA (M := M))›) with ⟨sa0⟩
        exact ⟨sa0, by simp⟩
    )
      (fun sa : SA (M := M) => |Q sa - R sa|)) := by
  classical
  -- This should be a short proof by chaining:
  --   |E[f]-E[g]| ≤ sup_{s'} |f(s')-g(s')|
  -- then use the previous lemma to bound each |nextMax' Q s' - nextMax' R s'|
  sorry

/-
Step 3:
Show Tq is γ-Lipschitz (contraction) in sup metric on QSpace.
This mirrors your `Topt_is_contraction`.
-/
theorem Tq_is_contraction :
  IsContraction (X := QSpace (M := M)) (T := Tq (M := M)) (γ := M.γ) := by
  classical
  refine
    { nonneg := M.γ_nonneg
      lt_one := M.γ_lt_one
      lipschitz := by
        -- same pattern: `LipschitzWith.of_dist_le_mul`
        -- and use a `dist_eq_sup` lemma specialized to `SA → ℝ`.
        sorry }  -- keep skeleton

/-
Step 4:
Use Banach fixed point to define unique Q* as fixed point of Tq.
-/
theorem exists_unique_Qstar :
  ∃! QStar : QSpace (M := M), Tq (M := M) QStar = QStar := by
  classical
  let K : ℝ≥0 := ⟨M.γ, M.γ_nonneg⟩
  have hContr : ContractingWith K (Tq (M := M)) := by
    simpa using
      IsContraction.toContractingWith
        (X := QSpace (M := M)) (T := Tq (M := M)) (γ := M.γ)
        (Tq_is_contraction (M := M))
  let QStar := ContractingWith.fixedPoint (f := Tq (M := M)) (K := K) hContr
  refine ⟨QStar, ?fix, ?uniq⟩
  · exact (ContractingWith.fixedPoint_isFixedPt (K := K) (f := Tq (M := M)) hContr).eq
  · intro Q hQ
    simpa using
      ContractingWith.fixedPoint_unique
        (K := K) (f := Tq (M := M)) hContr (x := Q) (hx := hQ)

end Contraction

section QLearningUpdate

variable (M : MDP)

/-
Now define the *sample-based* Q-learning update (one-step, one coordinate).

We work with the sigma index `sa : SA` and do the usual:
  Q_{t+1}(sa_t) = Q_t(sa_t) + α_t ( target_t - Q_t(sa_t) )
where
  target_t = r_t + γ * max_{a'} Q_t(s_{t+1},a')
and other coordinates unchanged.

This is the object you’ll use to relate the recursion to the Bellman operator Tq.
-/

open scoped Classical

/-- One-step Q-learning update at index `sa` with sample `(r, s')` and step size `α`. -/
noncomputable def qLearnStep
    (Q : QSpace (M := M))
    (sa : SA (M := M))        -- (s_t,a_t)
    (r : ℝ) (s' : M.S)        -- reward and next state
    (α : ℝ) : QSpace (M := M) :=
  fun sb =>
    if h : sb = sa then
      Q sb + α * (r + M.γ * nextMax' (M := M) Q s' - Q sb)
    else
      Q sb

/-
A “trajectory” / “sample stream” can be represented many ways.
For a minimal skeleton: assume you are given sequences:
  sa_t : ℕ → SA
  r_t  : ℕ → ℝ
  s'_t : ℕ → S
  α_t  : ℕ → ℝ
and define recursion.
-/
structure SampleStream (M : MDP) where
  sa   : ℕ → SA (M := M)
  r    : ℕ → ℝ
  s'   : ℕ → M.S
  α    : ℕ → ℝ

/-- Iterated Q-learning from initial Q0 using a sample stream. -/
noncomputable def QIter (Q0 : QSpace (M := M)) (ω : SampleStream M) : ℕ → QSpace (M := M)
  | 0       => Q0
  | (t + 1) => qLearnStep (M := M) (QIter Q0 ω t) (ω.sa t) (ω.r t) (ω.s' t) (ω.α t)

end QLearningUpdate

section ConvergenceSkeleton

variable (M : MDP)
local notation "QSpace" => QSpace (M := M)

/-
This section is the “proof plan” you described:

(1) Rewrite update as:
    Q_{t+1}(sa_t) = (1-α_t) Q_t(sa_t) + α_t ( (Tq Q_t)(sa_t) + noise_t )
(2) Show noise is a martingale difference (under correct filtration/model).
(3) Apply an asynchronous stochastic approximation theorem for contractions.
(4) Conclude Q_t → Q* (a.s. / in probability / etc).

We keep everything as placeholders so you can fill in with Mathlib later.
-/

/-- Robbins–Monro step-size condition at each visited coordinate (placeholder). -/
def RobbinsMonro (ω : SampleStream M) : Prop :=
  True  -- TODO: replace by ∀ sa, (∑' t in visits sa, α_t = ∞) ∧ (∑' α_t^2 < ∞)

/-- Infinite exploration / each (s,a) updated infinitely often (placeholder). -/
def InfiniteVisits (ω : SampleStream M) : Prop :=
  True  -- TODO: formalize using `Set.Infinite { t | ω.sa t = sa }` for all sa

/-- Bounded rewards assumption (placeholder). -/
def BoundedRewards (M : MDP) : Prop :=
  True  -- TODO: ∃ Rmax, ∀ s a, |r s a| ≤ Rmax

/-- Noise term definition (placeholder): target - conditional expectation target. -/
def Noise (Q : QSpace) (ω : SampleStream M) (t : ℕ) : ℝ :=
  0  -- TODO: define using conditional expectation in `ProbabilityTheory`

/-
Key lemma skeleton: “mean update equals Bellman operator”.
This is where you connect the conditional expectation of the sample target to `(Tq Q_t)(sa_t)`.
-/
lemma condExp_target_eq_Tq (Q : QSpace) (ω : SampleStream M) (t : ℕ) :
  True := by
  -- TODO: formal statement in Mathlib probability:
  --   E[ r_t + γ max Q(s'_{t+1},·) | F_t, sa_t ] = (Tq Q)(sa_t)
  trivial

/-
Key lemma skeleton: noise is martingale difference.
-/
lemma noise_martingaleDiff (Q : QSpace) (ω : SampleStream M) :
  True := by
  -- TODO: show `E[Noise_t | F_t] = 0`
  trivial

/-
Asynchronous SA convergence theorem: placeholder.
You’ll either:
- use an existing Mathlib theorem (if available), or
- port a theorem specialized to contractions,
- or prove a bespoke contraction-based SA lemma.

This is the “big hammer” step.
-/
theorem qLearning_converges_skeleton
    (Q0 : QSpace) (ω : SampleStream M)
    (hRM : RobbinsMonro (M := M) ω)
    (hVis : InfiniteVisits (M := M) ω)
    (hB : BoundedRewards (M := M)) :
    ∃ QStar : QSpace, Tq (M := M) QStar = QStar ∧
      Tendsto (fun t => QIter (M := M) Q0 ω t) atTop (nhds QStar) := by
  classical
  -- Plan:
  -- 1) get unique fixed point QStar from contraction
  -- 2) show recursion is an asynchronous stochastic approximation to Tq
  -- 3) apply SA theorem to obtain convergence
  rcases exists_unique_Qstar (M := M) with ⟨QStar, hfix, huniq⟩
  refine ⟨QStar, hfix, ?_⟩
  -- TODO: replace `sorry` with SA convergence result
  sorry

end ConvergenceSkeleton

end QLearning
end MDP
