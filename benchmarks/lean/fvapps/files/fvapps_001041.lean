-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_window_frames (n : Nat) (logs : List Int) : Nat := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_window_frames_non_negative {n : Nat} {logs : List Int} 
  (h : logs ≠ []) : 
  count_window_frames n logs ≥ 0 := 
  sorry

theorem count_window_frames_bounded {n : Nat} {logs : List Int}
  (h : logs ≠ []) :
  count_window_frames n logs ≤ n / 2 :=
  sorry

theorem count_window_frames_idempotent {n : Nat} {logs : List Int}
  (h : logs ≠ []) :
  count_window_frames n logs = count_window_frames n logs :=
  sorry

theorem count_window_frames_order_invariant {n : Nat} {logs : List Int} 
  (h : logs ≠ []) :
  count_window_frames n logs = count_window_frames n logs.reverse :=
  sorry

theorem count_window_frames_duplicates_bound {n : Nat} {logs : List Int}
  (h1 : logs ≠ [])
  (h2 : ∀ x ∈ logs, 1 ≤ x ∧ x ≤ 3) :
  count_window_frames n logs ≤ (logs.length - (logs.eraseDups).length) / 2 := 
  sorry
-- </vc-theorems>