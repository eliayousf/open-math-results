import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Set.Card
import Mathlib.Data.Sym.Sym2

/-!
# How does the distribution of Erdős number evolve over time ? How to build a model to fit the real data ?

Source: https://mathoverflow.net/questions/100099 (Hao Chen, 20 June 2012).
Credit: @chris01-dev

The question is mostly a request for a model, and it leaves the rule that picks the coauthors
of each article open. The one precise claim it makes about the evolution of `E(n,t)` is its
first listed fact: for every `n > 0` there is a time `T(n)` such that `E(n,t)` is constant
for `t > T(n)`. That claim is stated here, under exactly the assumptions the question lists:

* only cooperations between two mathematicians: an article is an unordered pair of two
  different mathematicians;
* every year the number of new mathematicians is a constant `a` and the number of new
  articles is a constant `p`;
* every mathematician has the same career length of `L` years.

Since the question fixes no rule for who writes with whom, the claim is stated for every
collaboration history that satisfies these assumptions (so it covers each outcome of any
random rule). Time is counted in whole years `0, 1, 2, ...`. An article of year `y` needs
both authors in career in year `y`. As in the Erdős Number Project table quoted on the source
page, and as the remark `T(1) ≤ 1996` there requires, `E(n,t)` counts every mathematician
whose Erdős number is `n` at time `t`, whether still in career or not.

Not stated here: the second listed item (whether the average Erdős number grows linearly)
and the request for a model fitting real data. Both depend on a choice of random rule that
the source does not make.
-/

namespace OMA.S_mo_100099

/-- A mathematician is named by the first year of the career and an index among the `a`
mathematicians who start in that year. So exactly `a` new mathematicians arrive every year. -/
abbrev Mathematician (a : ℕ) : Type := ℕ × Fin a

/-- `v` is in career during year `y`: the career lasts the `L` years `v.1, ..., v.1 + L - 1`. -/
def Active {a : ℕ} (L : ℕ) (v : Mathematician a) (y : ℕ) : Prop :=
  v.1 ≤ y ∧ y < v.1 + L

/-- `paper y j` is the `j`-th of the `p` articles of year `y`. Every article has two different
authors, and both are in career in the year of the article. -/
def Admissible {a p : ℕ} (L : ℕ) (paper : ℕ → Fin p → Sym2 (Mathematician a)) : Prop :=
  ∀ y j, ¬ (paper y j).IsDiag ∧ ∀ v ∈ paper y j, Active L v y

/-- The collaboration graph at time `t`: two mathematicians are joined when they wrote a
joint article in some year `y ≤ t`. -/
def collab {a p : ℕ} (paper : ℕ → Fin p → Sym2 (Mathematician a)) (t : ℕ) :
    SimpleGraph (Mathematician a) :=
  SimpleGraph.fromRel fun u v => ∃ y, y ≤ t ∧ ∃ j, paper y j = s(u, v)

/-- `E erdos paper n t` is the number of mathematicians whose Erdős number at time `t`
(the distance to `erdos` in the collaboration graph at time `t`) equals `n`. -/
noncomputable def E {a p : ℕ} (erdos : Mathematician a)
    (paper : ℕ → Fin p → Sym2 (Mathematician a)) (n t : ℕ) : ℕ∞ :=
  {v : Mathematician a | (collab paper t).edist erdos v = (n : ℕ∞)}.encard

/-- For every `n > 0` there is a time `T` after which `E(n,t)` is a constant (finite) number. -/
theorem main :
    ∀ (a p L : ℕ) (erdos : Mathematician a) (paper : ℕ → Fin p → Sym2 (Mathematician a)),
      Admissible L paper →
        ∀ n : ℕ, 0 < n → ∃ T c : ℕ, ∀ t : ℕ, T < t → E erdos paper n t = (c : ℕ∞) := by
  sorry

end OMA.S_mo_100099
