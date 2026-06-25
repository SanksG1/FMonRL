import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice


universe u

variable {U : Type u}
variable (prop : Set U)
variable (neg : U → U)
variable (bin : U → U → U)


def IsClosed (S : Set U) : Prop :=
  (∀ φ, φ ∈ S → neg φ ∈ S) ∧
  (∀ φ₁ φ₂, φ₁ ∈ S → φ₂ ∈ S → bin φ₁ φ₂ ∈ S)

def FormNC : Set U :=
  ⋂ S ∈ { S : Set U | prop ⊆ S ∧ IsClosed neg bin S }, S



lemma formNC_contains_prop :
    prop ⊆ FormNC prop neg bin := by
  intro φ hφ
  simp only [FormNC, Set.mem_iInter]
  intro S hS
  exact hS.1 hφ

lemma formNC_is_closed :
    IsClosed neg bin (FormNC prop neg bin) := by
  constructor
  · intro φ hφ
    simp only [FormNC, Set.mem_iInter] at *
    intro S hS
    exact hS.2.1 φ (hφ S hS)
  · intro φ₁ φ₂ h₁ h₂
    simp only [FormNC, Set.mem_iInter] at *
    intro S hS
    exact hS.2.2 φ₁ φ₂ (h₁ S hS) (h₂ S hS)

lemma formNC_smallest
    (S : Set U) (hS_prop : prop ⊆ S) (hS_closed : IsClosed neg bin S) :
    FormNC prop neg bin ⊆ S := by
  intro φ hφ
  simp only [FormNC, Set.mem_iInter] at hφ
  exact hφ S ⟨hS_prop, hS_closed⟩


lemma formNC_well_defined :
    ∃! S : Set U,
      prop ⊆ S ∧
      IsClosed neg bin S ∧
      ∀ T : Set U, prop ⊆ T → IsClosed neg bin T → S ⊆ T := by
  refine ⟨FormNC prop neg bin,
          ⟨formNC_contains_prop prop neg bin,
           formNC_is_closed prop neg bin,
           formNC_smallest prop neg bin⟩,
          ?_⟩
  intro S ⟨hS_prop, hS_closed, hS_smallest⟩
  apply Set.eq_of_subset_of_subset
  · exact hS_smallest _ (formNC_contains_prop prop neg bin) (formNC_is_closed prop neg bin)
  · exact formNC_smallest prop neg bin S hS_prop hS_closed




def FormLayer : ℕ → Set U
  | 0     => prop
  | n + 1 => FormLayer n
              ∪ { φ | ∃ ψ ∈ FormLayer n, φ = neg ψ }
              ∪ { φ | ∃ ψ₁ ∈ FormLayer n, ∃ ψ₂ ∈ FormLayer n, φ = bin ψ₁ ψ₂ }

def FormC : Set U :=
  ⋃ i, FormLayer prop neg bin i



lemma formLayer_mono :
    ∀ i, FormLayer prop neg bin i ⊆ FormLayer prop neg bin (i + 1) := by
  intro i φ hφ
  simp only [FormLayer]
  left; left
  exact hφ

lemma formLayer_le {i j : ℕ} (hij : i ≤ j) :
    FormLayer prop neg bin i ⊆ FormLayer prop neg bin j := by
  induction hij with
  | refl        => exact le_refl _
  | step _ ih   => exact ih.trans (formLayer_mono prop neg bin _)



lemma formC_contains_prop :
    prop ⊆ FormC prop neg bin := by
  intro φ hφ
  simp only [FormC, Set.mem_iUnion]
  exact ⟨0, hφ⟩

lemma formC_is_closed :
    IsClosed neg bin (FormC prop neg bin) := by
  constructor
  · intro φ hφ
    simp only [FormC, Set.mem_iUnion] at *
    obtain ⟨k, hk⟩ := hφ
    refine ⟨k + 1, ?_⟩
    simp only [FormLayer]
    left; right
    exact ⟨φ, hk, rfl⟩
  · intro φ₁ φ₂ h₁ h₂
    simp only [FormC, Set.mem_iUnion] at *
    obtain ⟨k₁, hk₁⟩ := h₁
    obtain ⟨k₂, hk₂⟩ := h₂
    refine ⟨max k₁ k₂ + 1, ?_⟩
    simp only [FormLayer]
    right
    exact ⟨φ₁,
           formLayer_le prop neg bin (Nat.le_max_left k₁ k₂) hk₁,
           φ₂,
           formLayer_le prop neg bin (Nat.le_max_right k₁ k₂) hk₂,
           rfl⟩

lemma formLayer_subset_formNC :
    ∀ i, FormLayer prop neg bin i ⊆ FormNC prop neg bin := by
  intro i
  induction i with
  | zero      => exact formNC_contains_prop prop neg bin
  | succ n ih =>
      intro φ hφ
      simp only [FormLayer] at hφ
      rcases hφ with ⟨hbase | hneg⟩ | hbin
      · exact ih hbase
      · obtain ⟨ψ, hψ, rfl⟩ := hneg
        exact (formNC_is_closed prop neg bin).1 ψ (ih hψ)
      · obtain ⟨ψ₁, hψ₁, ψ₂, hψ₂, rfl⟩ := hbin
        exact (formNC_is_closed prop neg bin).2 ψ₁ ψ₂ (ih hψ₁) (ih hψ₂)

lemma formC_subset_formNC :
    FormC prop neg bin ⊆ FormNC prop neg bin := by
  intro φ hφ
  simp only [FormC, Set.mem_iUnion] at hφ
  obtain ⟨i, hi⟩ := hφ
  exact formLayer_subset_formNC prop neg bin i hi



theorem formC_eq_formNC :
    FormC prop neg bin = FormNC prop neg bin := by
  apply Set.eq_of_subset_of_subset
  · exact formC_subset_formNC prop neg bin
  · exact formNC_smallest prop neg bin
        (FormC prop neg bin)
        (formC_contains_prop prop neg bin)
        (formC_is_closed prop neg bin)
