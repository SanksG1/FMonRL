import BasicLogic.SAT

namespace PropLogic


structure Graph (V : Type u) where
  E : Set (V × V)


abbrev Color := Fin 3


/-! Each SAT variable is a pair (v, c) -/
abbrev ColorVar (V : Type u) := V × Color


def coloringToValuation
    {V : Type u}
    (c : V → Color) :
    Valuation (ColorVar V)
| (v, k) =>
    decide (c v = k)


variable {V : Type u}

/- No edge has same color on both endpoints -/
def edgeConstraint (G : Graph V) (v : Valuation (ColorVar V)) : Prop :=
  ∀ p ∈ G.E,
    let ⟨a,b⟩ := p
    ∀ k : Color,
      ¬ (v (a,k) = true ∧ v (b,k) = true)


/- Every vertex has at least one color -/
def atLeastOneColor (v : Valuation (ColorVar V)) : Prop :=
  ∀ a : V,
    (v (a,0) = true ∨ v (a,1) = true ∨ v (a,2) = true)


/- No vertex has two colors simultaneously -/
def atMostOneColor (v : Valuation (ColorVar V)) : Prop :=
  ∀ a : V,
    (¬ (v (a,0) = true ∧ v (a,1) = true)) ∧
    (¬ (v (a,1) = true ∧ v (a,2) = true)) ∧
    (¬ (v (a,0) = true ∧ v (a,2) = true))


/- Full 3-color validity -/
def Valid3Coloring (G : Graph V) (v : Valuation (ColorVar V)) : Prop :=
  edgeConstraint G v ∧ atLeastOneColor v ∧ atMostOneColor v

/-- A valuation encodes a coloring assignment -/
def PsiVal
    (G : Graph V)
    (v : Valuation (ColorVar V)) : Prop :=
  edgeConstraint G v ∧
  atLeastOneColor v ∧
  atMostOneColor v
