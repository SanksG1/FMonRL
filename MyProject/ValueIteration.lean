import Mathlib.Data.NNReal.Defs
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Contracting


open scoped NNReal
open scoped BigOperators
open Filter


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

section Abstract

-- We want access to `dist` and to Banach's fixed point theorems,
-- so we work in a complete metric space with a point.
-- Disable the linter that complains about automatically included section
-- variables that are not used by every declaration in this section.
set_option linter.unusedSectionVars false
variable {X : Type*} [MetricSpace X]

/-- A self-map `T` with Lipschitz constant `γ < 1`.  We phrase the Lipschitz
    condition using `LipschitzWith` so it matches `ContractingWith`. -/
structure IsContraction (T : X → X) (γ : ℝ) : Prop where
  nonneg    : 0 ≤ γ
  lt_one    : γ < 1
  lipschitz : LipschitzWith ⟨γ, nonneg⟩ T

namespace IsContraction

/-- Turn our `IsContraction` into mathlib's `ContractingWith`, which gives
    all the Banach fixed-point API. -/
lemma toContractingWith {T : X → X} {γ : ℝ}
    (h : IsContraction (X := X) T γ) :
    ContractingWith ⟨γ, h.nonneg⟩ T := by
  -- `ContractingWith K T` is `< 1 ∧ LipschitzWith K T`.
  exact ⟨by simpa using h.lt_one, h.lipschitz⟩

end IsContraction

/-- Picard iteration of a map `T` starting from `x₀`. -/
def picard (T : X → X) (x0 : X) : ℕ → X
  | 0       => x0
  | (n + 1) => T (picard T x0 n)

/-- Picard iteration agrees with `Function.iterate`. This is handy because
    mathlib’s contraction machinery is phrased for `f^[n]`. -/
lemma picard_eq_iterate (T : X → X) (x0 : X) :
    picard T x0 = fun n => (T^[n]) x0 := by
  funext n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      -- `Function.iterate_succ_apply'`:
      --   `T^[n+1] x0 = T (T^[n] x0)`
      simp [picard, Function.iterate_succ_apply', ih]

/-- Existence and uniqueness of a fixed point for a contraction. -/
theorem contraction_has_unique_fixedPoint
  {T : X → X} {γ : ℝ} (h : IsContraction (X := X) T γ)
  [CompleteSpace X] [Nonempty X] :
  ∃! xStar, T xStar = xStar := by
  classical
  set K : ℝ≥0 := ⟨γ, h.nonneg⟩ with hKdef
  have hContr : ContractingWith K T := by
    simpa [hKdef] using
      IsContraction.toContractingWith (X := X) (T := T) (γ := γ) h
  refine ⟨ContractingWith.fixedPoint (f := T) (K := K) hContr, ?hx, ?uniq⟩
  · -- fixed point equation
    exact
      (ContractingWith.fixedPoint_isFixedPt (K := K) (f := T) hContr).eq
  · intro y hy
    simpa using
      ContractingWith.fixedPoint_unique
        (K := K) (f := T) hContr (x := y) (hx := hy)

/-- Picard iterates converge to the unique fixed point of a contraction map. -/
theorem picard_converges_to_fixedPoint
  {T : X → X} {γ : ℝ} (h : IsContraction (X := X) T γ) (x0 : X)
  [CompleteSpace X] [Nonempty X] :
  ∃ xStar, T xStar = xStar ∧
    Tendsto (fun n => picard T x0 n) atTop (nhds xStar) := by
  classical
  set K : ℝ≥0 := ⟨γ, h.nonneg⟩ with hKdef
  have hContr : ContractingWith K T := by
    simpa [hKdef] using IsContraction.toContractingWith (X := X) (T := T) (γ := γ) h
  let xStar := ContractingWith.fixedPoint (f := T) (K := K) hContr
  have hxStar : T xStar = xStar :=
    (ContractingWith.fixedPoint_isFixedPt (K := K) (f := T) hContr).eq
  have hconv_iter :
      Tendsto (fun n => T^[n] x0) atTop (nhds xStar) :=
    ContractingWith.tendsto_iterate_fixedPoint
      (K := K) (f := T) hContr x0
  refine ⟨xStar, hxStar, ?_⟩
  -- Picard = iterate, then reuse convergence result.
  simpa [picard_eq_iterate T x0] using hconv_iter

/-- A standard a priori error bound for Picard iteration.
We wrap mathlib’s `ContractingWith.apriori_dist_iterate_fixedPoint_le`
and rewrite everything in terms of `γ` and `picard`. -/
theorem picard_error_bound
  {T : X → X} {γ : ℝ} (h : IsContraction (X := X) T γ) (x0 : X)
  [CompleteSpace X] [Nonempty X] :
  let xStar := Classical.choose
    (ExistsUnique.exists (contraction_has_unique_fixedPoint (X := X) h))
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n, dist (picard T x0 n) xStar ≤ (γ ^ n) * C := by
  classical
  intro xStar
  set K : ℝ≥0 := ⟨γ, h.nonneg⟩ with hKdef
  have hContr : ContractingWith K T := by
    simpa [hKdef] using IsContraction.toContractingWith (X := X) (T := T) (γ := γ) h

  -- canonical fixed point
  let yStar := ContractingWith.fixedPoint (f := T) (K := K) hContr
  have hy_fix : T yStar = yStar :=
    (ContractingWith.fixedPoint_isFixedPt (K := K) (f := T) hContr).eq

  -- `xStar` from `ExistsUnique` is also a fixed point, hence equal to `yStar`.
  have hx_fix : T xStar = xStar :=
    (Classical.choose_spec
      (ExistsUnique.exists (contraction_has_unique_fixedPoint (X := X) h)))
  have h_eq : xStar = yStar :=
    ExistsUnique.unique (contraction_has_unique_fixedPoint (X := X) h)
      hx_fix hy_fix

  -- `1 - γ > 0`
  have hK_pos : 0 < (1 - γ) := by
    have hpos := ContractingWith.one_sub_K_pos
      (K := K) (f := T) hContr
    simpa [hKdef] using hpos

  -- standard constant
  let C : ℝ := dist x0 (T x0) / (1 - γ)
  have hC0 : 0 ≤ C := by
    have hden : 0 ≤ (1 - γ) := le_of_lt hK_pos
    exact div_nonneg dist_nonneg hden

  refine ⟨C, hC0, ?_⟩
  intro n

  -- a priori estimate on iterates from mathlib
  have happ_iter :
      dist (T^[n] x0) yStar
        ≤ dist x0 (T x0) * (γ ^ n) / (1 - γ) := by
    have h' :=
      ContractingWith.apriori_dist_iterate_fixedPoint_le
        (K := K) (f := T) hContr x0 n
    simpa [hKdef] using h'

  -- relate `picard` and `iterate`
  have h_pic_iter :
      picard T x0 n = (T^[n]) x0 := by
    simpa using congrArg (fun f => f n) (picard_eq_iterate T x0)

  have hdist :
      dist (picard T x0 n) xStar
        = dist (T^[n] x0) yStar := by
    simp [h_pic_iter, h_eq]

  -- rewrite RHS as `(γ^n) * C`
  have happ_C :
      dist (T^[n] x0) yStar
        ≤ (γ ^ n) * C := by
    have := happ_iter
    have hR :
        dist x0 (T x0) * γ ^ n / (1 - γ)
          = (γ ^ n) * C := by
      unfold C
      simp [div_eq_mul_inv, mul_left_comm, mul_assoc]
    simpa [hR] using this

  simpa [hdist] using happ_C

end Abstract

/-! ## Model-specific definitions -/

section Model

instance instDecidableEqS (M : MDP) : DecidableEq M.S := M.decS
instance instFintypeS (M : MDP) : Fintype     M.S := M.finS
instance instDecidableEqA (M : MDP) : DecidableEq M.A := M.decA

/-- For later use of abstract theorems, we want `(S → ℝ)` to be nonempty. -/
instance instNonemptyValSpace (M : MDP) : Nonempty (M.S → ℝ) :=
  ⟨fun _ => 0⟩

variable (M : MDP)
local notation "S" => M.S
local notation "A" => M.A

/-- Expected value of `V` under a PMF `p`. -/
def expVal (V : S → ℝ) (p : PMF S) : ℝ :=
  ∑ s, (p s).toReal * V s

/-- Optimal Bellman operator. -/
def Topt (V : S → ℝ) : S → ℝ :=
  fun s =>
    (M.Aset s).sup' (M.Aset_nonempty s) /- Check sup' does take the max -/
      (fun a => M.r s a + M.γ * expVal M V (M.P s a))

end Model

/-! ## Lipschitz / contraction bits for `Topt` -/

section LipschitzBits

variable (M : MDP)
local notation "S" => M.S

private lemma univ_nonempty_S : (Finset.univ : Finset S).Nonempty := by
  classical
  rcases M.S_nonempty with ⟨s0⟩
  exact ⟨s0, by simp⟩

lemma expVal_diff_le_sup (V W : S → ℝ) (p : PMF S) :
  |expVal M V p - expVal M W p|
    ≤ (Finset.univ.sup' (univ_nonempty_S M) (fun s : S => |V s - W s|)) := by
  classical
  -- sup norm of V - W
  set supVal : ℝ :=
    Finset.univ.sup' (univ_nonempty_S M) (fun s : S => |V s - W s|) with hsup

  -- every coordinate is ≤ supVal
  have hcoord : ∀ s : S, |V s - W s| ≤ supVal := fun s =>
    Finset.le_sup'
      (s := Finset.univ)
      (f := fun t : S => |V t - W t|)
      (b := s)
      (by simp)

  -- rewrite the difference of expectations as one sum
  have hdiff :
      expVal M V p - expVal M W p
        = ∑ s, (p s).toReal * (V s - W s) := by
    unfold expVal
    have :=
      (Finset.sum_sub_distrib
        (s := (Finset.univ : Finset S))
        (f := fun s : S => (p s).toReal * V s)
        (g := fun s : S => (p s).toReal * W s))
    -- ∑ p V - ∑ p W = ∑ (pV - pW) = ∑ p (V-W)
    simp [this, mul_sub]  -- `simp` can turn the difference into `p*(V-W)`

  -- |∑ x_s| ≤ ∑ |x_s|
  have h_abs_sum :
      |∑ s, (p s).toReal * (V s - W s)|
        ≤ ∑ s, |(p s).toReal * (V s - W s)| := by
    simpa using
      (Finset.abs_sum_le_sum_abs
        (s := (Finset.univ : Finset S))
        (f := fun s : S => (p s).toReal * (V s - W s)))

  -- move abs inside the product, using (p s).toReal ≥ 0
  have h_abs_mul :
      ∑ s, |(p s).toReal * (V s - W s)|
        = ∑ s, (p s).toReal * |V s - W s| := by
    refine Finset.sum_congr rfl ?_
    intro s _
    have hnonneg : 0 ≤ (p s).toReal := ENNReal.toReal_nonneg
    simp [abs_mul, abs_of_nonneg hnonneg]

  -- bound each term by (p s).toReal * supVal
  have h_sum_le :
      ∑ s, (p s).toReal * |V s - W s|
        ≤ ∑ s, (p s).toReal * supVal := by
    refine Finset.sum_le_sum ?_
    intro s _
    exact mul_le_mul_of_nonneg_left (hcoord s) ENNReal.toReal_nonneg

  -- turn ∑ p_s * supVal into supVal * ∑ p_s, and use ∑ p_s = 1
  have h_sum_const :
      ∑ s, (p s).toReal * supVal
        = supVal * ∑ s, (p s).toReal := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Finset.sum_mul
        (s := (Finset.univ : Finset S))
        (f := fun s : S => (p s).toReal)
        (a := supVal)).symm

  -- ∑ s (p s).toReal = 1
  have hsum_probs : ∑ s, (p s).toReal = 1 := by
    -- First, sum in ENNReal using the PMF property
    have hEN : (∑ s, p s) = (1 : ENNReal) := by
      have htsum : (∑' s, p s) = (1 : ENNReal) := p.property.tsum_eq
      simpa [tsum_fintype] using htsum

    -- relate (∑ p s).toReal to ∑ (p s).toReal
    have h_toReal_sum :
        ((∑ s, p s).toReal) = ∑ s, (p s).toReal := by
      -- need finiteness to use `toReal_sum`
      have hfinite :
          ∀ a ∈ (Finset.univ : Finset S), p a ≠ (⊤ : ENNReal) := by
        intro a _
        exact PMF.apply_ne_top p a
      have :=
        ENNReal.toReal_sum
          (s := (Finset.univ : Finset S))
          (f := fun s : S => p s)
          (hf := hfinite)
      simpa using this

    -- apply toReal to (∑ p s = 1)
    have h_toReal_one : ((∑ s, p s).toReal) = (1 : ℝ) := by
      have := congrArg ENNReal.toReal hEN
      simpa using this

    calc
      ∑ s, (p s).toReal
          = ((∑ s, p s).toReal) := by simp [h_toReal_sum]
      _ = 1 := h_toReal_one

  have h_final :
      ∑ s, (p s).toReal * |V s - W s| ≤ supVal := by
    calc
      ∑ s, (p s).toReal * |V s - W s|
          ≤ ∑ s, (p s).toReal * supVal := h_sum_le
      _ = supVal * ∑ s, (p s).toReal := h_sum_const
      _ = supVal * 1 := by simp [hsum_probs]
      _ = supVal := by simp

  -- chain everything together
  have h_main :
      |expVal M V p - expVal M W p| ≤ supVal := by
    calc
      |expVal M V p - expVal M W p|
          = |∑ s, (p s).toReal * (V s - W s)| := by
              simp [hdiff]
      _ ≤ ∑ s, |(p s).toReal * (V s - W s)| := h_abs_sum
      _ = ∑ s, (p s).toReal * |V s - W s| := h_abs_mul
      _ ≤ supVal := h_final

  simpa [supVal, hsup] using h_main

lemma dist_eq_sup (V W : S → ℝ) :
  dist V W
    = (Finset.univ.sup' (univ_nonempty_S M) (fun s : S => |V s - W s|)) := by
  classical
  let hne : (Finset.univ : Finset S).Nonempty := univ_nonempty_S M
  let supVal : ℝ := Finset.univ.sup' hne (fun s : S => |V s - W s|)

  -- 1) 0 ≤ supVal
  have h0 : 0 ≤ supVal := by
    rcases M.S_nonempty with ⟨s0⟩
    have : |V s0 - W s0| ≤ supVal :=
      Finset.le_sup'
        (s := Finset.univ)
        (f := fun s : S => |V s - W s|)
        (b := s0)
        (by simp)
    exact (abs_nonneg _).trans this

  -- 2) each coordinate distance ≤ supVal
  have hcoords : ∀ s : S, dist (V s) (W s) ≤ supVal := by
    intro s
    have : |V s - W s| ≤ supVal :=
      Finset.le_sup'
        (s := Finset.univ)
        (f := fun t : S => |V t - W t|)
        (b := s)
        (by simp)
    simpa [Real.dist_eq] using this

  -- 3) dist(V,W) ≤ supVal
  have h1 : dist V W ≤ supVal :=
    (dist_pi_le_iff (f := V) (g := W) (r := supVal) h0).2 hcoords

  -- 4) supVal ≤ dist(V,W)
  have h2 : supVal ≤ dist V W := by
    refine
      Finset.sup'_le
        (s := Finset.univ)
        (H := hne)
        (f := fun s : S => |V s - W s|)
        ?_
    intro s _
    have : dist (V s) (W s) ≤ dist V W :=
      dist_le_pi_dist V W s
    simpa [Real.dist_eq] using this

  simpa [supVal, hne] using le_antisymm h1 h2

end LipschitzBits

/-! ## `Topt` is a contraction on `(S → ℝ)` -/

section Contraction

variable (M : MDP)
local notation "S" => M.S

theorem Topt_is_contraction :
  IsContraction (X := (S → ℝ)) (T := Topt M) (γ := M.γ) := by
  refine
    { nonneg := M.γ_nonneg
      lt_one := M.γ_lt_one
      lipschitz := by
        classical
        -- Use `LipschitzWith.of_dist_le_mul`.
        refine LipschitzWith.of_dist_le_mul ?bound
        intro V W

        -- sup-norm of V - W
        let supVW : ℝ :=
          Finset.univ.sup' (univ_nonempty_S M) (fun s : S => |V s - W s|)

        have hdist_VW :
            dist V W = supVW := by
          simpa [supVW] using (dist_eq_sup (M := M) V W)

        -- Step 1: pointwise bound on the Bellman operator.
        have h_coord :
            ∀ s : S,
              |Topt M V s - Topt M W s|
                ≤ M.γ * supVW := by
          intro s
          -- Action set at s
          let B : Finset M.A := M.Aset s
          have hBne : B.Nonempty := M.Aset_nonempty s

          -- Q-values under V and W
          let fV : M.A → ℝ :=
            fun a => M.r s a + M.γ * expVal M V (M.P s a)
          let fW : M.A → ℝ :=
            fun a => M.r s a + M.γ * expVal M W (M.P s a)

          -- their sups over actions (= Topt at s)
          let sx : ℝ := B.sup' hBne (fun a => fV a)
          let sy : ℝ := B.sup' hBne (fun a => fW a)

          have hsx : sx = Topt M V s := rfl
          have hsy : sy = Topt M W s := rfl

          -- one-sided inequality: sx ≤ sy + γ * supVW
          have h_sx_le : sx ≤ sy + M.γ * supVW := by
            refine
              Finset.sup'_le
                (s := B) (H := hBne) (f := fun a => fV a) ?_
            intro a ha
            -- fW a ≤ sy
            have hfW_le_sy : fW a ≤ sy :=
              Finset.le_sup'
                (s := B)
                (f := fun b => fW b)
                (b := a)
                (by simpa [B])

            -- |E_V - E_W| ≤ supVW
            have h_exp_abs :
                |expVal M V (M.P s a) - expVal M W (M.P s a)|
                  ≤ supVW := by
              simpa [supVW] using
                (expVal_diff_le_sup (M := M) V W (M.P s a))

            -- turn absolute bound into x ≤ y + supVW
            have h_exp_le :
                expVal M V (M.P s a)
                  ≤ expVal M W (M.P s a) + supVW := by
              set x := expVal M V (M.P s a)
              set y := expVal M W (M.P s a)
              have : x - y ≤ supVW :=
                (le_abs_self (x - y)).trans
                  (by simpa [x, y] using h_exp_abs)
              have := add_le_add_left this y
              simpa [x, y] using this


            have hγ_exp_le :
                M.γ * expVal M V (M.P s a)
                  ≤ M.γ * (expVal M W (M.P s a) + supVW) :=
              mul_le_mul_of_nonneg_left h_exp_le M.γ_nonneg

            -- fV a ≤ fW a + γ supVW
            have hfV_le :
                fV a ≤ fW a + M.γ * supVW := by
              have h_add :=
                add_le_add_left hγ_exp_le (M.r s a)
              simpa [fV, fW, mul_add, add_comm, add_left_comm, add_assoc] using h_add

            -- and fW a + γ supVW ≤ sy + γ supVW
            have hfW_sy_add :
                fW a + M.γ * supVW ≤ sy + M.γ * supVW :=
              add_le_add_right hfW_le_sy _
            exact le_trans hfV_le hfW_sy_add

          -- symmetric inequality: sy ≤ sx + γ * supVW
          have h_sy_le : sy ≤ sx + M.γ * supVW := by
            refine
              Finset.sup'_le
                (s := B) (H := hBne) (f := fun a => fW a) ?_
            intro a ha
            -- fV a ≤ sx
            have hfV_le_sx : fV a ≤ sx :=
              Finset.le_sup'
                (s := B)
                (f := fun b => fV b)
                (b := a)
                (by simpa [B])

            -- now bound |E_W - E_V| ≤ supVW
            have h_exp_abs :
                |expVal M W (M.P s a) - expVal M V (M.P s a)|
                  ≤ supVW := by
              simpa [supVW, abs_sub_comm] using
                (expVal_diff_le_sup (M := M) W V (M.P s a))

            have h_exp_le' :
                expVal M W (M.P s a)
                  ≤ expVal M V (M.P s a) + supVW := by
              set x := expVal M W (M.P s a) with hx
              set y := expVal M V (M.P s a) with hy
              have h1 : x - y ≤ |x - y| := le_abs_self _
              have h2 : |x - y| ≤ supVW := by
                simpa [hx, hy] using h_exp_abs
              have h3 : x - y ≤ supVW := le_trans h1 h2
              have h4 := add_le_add_left h3 y
              simpa [x, y] using h4

            have hγ_exp_le' :
                M.γ * expVal M W (M.P s a)
                  ≤ M.γ * (expVal M V (M.P s a) + supVW) :=
              mul_le_mul_of_nonneg_left h_exp_le' M.γ_nonneg

            have hfW_le :
                fW a ≤ fV a + M.γ * supVW := by
              have h_add :=
                add_le_add_left hγ_exp_le' (M.r s a)
              simpa [fV, fW, mul_add, add_comm, add_left_comm, add_assoc] using h_add

            have hfV_sx_add :
                fV a + M.γ * supVW ≤ sx + M.γ * supVW :=
              add_le_add_right hfV_le_sx _
            exact le_trans hfW_le hfV_sx_add

          -- convert the two one-sided bounds into an abs bound
          have h1 : sx - sy ≤ M.γ * supVW := by
            simpa [sub_eq_add_neg] using sub_le_sub_right h_sx_le sy
          have h2 : sy - sx ≤ M.γ * supVW := by
            simpa [sub_eq_add_neg] using sub_le_sub_right h_sy_le sx
          have hneg : -(M.γ * supVW) ≤ sx - sy := by
            simpa [sub_eq_add_neg] using neg_le_neg h2
          have h_abs : |sx - sy| ≤ M.γ * supVW :=
            abs_le.mpr ⟨hneg, h1⟩

          simpa [hsx, hsy] using h_abs

        -- Step 2: sup over states gives dist bound for Topt V, Topt W
        have h_sup_Topt :
            dist (Topt M V) (Topt M W)
              ≤ M.γ * supVW := by
          have hdist_sup :
              dist (Topt M V) (Topt M W)
                = Finset.univ.sup' (univ_nonempty_S M)
                    (fun s : S => |Topt M V s - Topt M W s|) :=
            dist_eq_sup (M := M) (Topt M V) (Topt M W)
          have hsup_le :
              Finset.univ.sup' (univ_nonempty_S M)
                  (fun s : S => |Topt M V s - Topt M W s|)
                ≤ M.γ * supVW := by
            refine
              Finset.sup'_le
                (s := Finset.univ)
                (H := univ_nonempty_S M)
                (f := fun s : S => |Topt M V s - Topt M W s|)
                ?_
            intro s _
            exact h_coord s
          simpa [hdist_sup] using hsup_le

        -- Step 3: replace supVW with dist V W
        have hfinal :
            dist (Topt M V) (Topt M W)
              ≤ M.γ * dist V W := by
          simpa [hdist_VW] using h_sup_Topt

        simpa using hfinal }


end Contraction

/-! ## Value iteration and its convergence/error bounds -/

section ValueIteration

variable (M : MDP)
local notation "S" => M.S

/-- Value iteration with starting value function `V0`. -/
def Viter (M : MDP) (V0 : M.S → ℝ) : ℕ → (M.S → ℝ)
  | 0       => V0
  | (n + 1) => Topt M (Viter M V0 n)

/-- Value iteration agrees with Picard iteration of `Topt`. -/
lemma Viter_eq_picard (V0 : S → ℝ) :
    Viter M V0 = picard (T := Topt M) V0 := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [Viter, picard, ih]

/-- Existence and uniqueness of the optimal value function `VStar`. -/
theorem exists_unique_Vstar :
  ∃! VStar : S → ℝ, Topt M VStar = VStar := by
  have h := Topt_is_contraction M
  simpa using
    (contraction_has_unique_fixedPoint
      (X := S → ℝ) (T := Topt M) (γ := M.γ) h)

/-- Convergence of value iteration to the optimal value function. -/
theorem valueIteration_converges (V0 : S → ℝ) :
  ∃ VStar : S → ℝ, Topt M VStar = VStar
    ∧ Tendsto (fun n => Viter M V0 n) atTop (nhds VStar) := by
  have h := Topt_is_contraction M
  rcases
    picard_converges_to_fixedPoint
      (X := S → ℝ) (T := Topt M) (γ := M.γ) h V0
    with ⟨VStar, hfix, hconv⟩
  refine ⟨VStar, hfix, ?_⟩
  simpa [Viter_eq_picard (M := M) V0] using hconv

/-- Quantitative error bound for value iteration. -/
theorem valueIteration_error_bound (V0 : S → ℝ) :
  let VStar := Classical.choose
    (ExistsUnique.exists (exists_unique_Vstar M))
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n, dist (Viter M V0 n) VStar ≤ (M.γ ^ n) * C := by
  intro VStar
  have h := Topt_is_contraction M

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

  have hV : Topt M VStar = VStar :=
    Classical.choose_spec (ExistsUnique.exists (exists_unique_Vstar M))

  have hEq : VStar = xStar :=
    (ExistsUnique.unique (exists_unique_Vstar M) hV (by simpa using hx)).symm

  rcases
    (picard_error_bound (X := S → ℝ) (T := Topt M) (γ := M.γ) h V0)
      with ⟨C, hC0, hbound⟩

  refine ⟨C, hC0, ?_⟩
  intro n
  simpa [Viter_eq_picard (M := M) V0, xStar, hEq] using hbound n


end ValueIteration

end MDP
