import OMAStatements.S_oeis_a128828

namespace A128828Proof

open OMA.S_oeis_a128828

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in
private theorem counterexample_count : a 17 = 4734 := by decide +kernel

end A128828Proof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a128828.main) := by
  intro h
  have hc := h 17 (by decide)
  rw [A128828Proof.counterexample_count] at hc
  exact (by decide : (511272 : ℤ) ≠ 534600) hc
