/-
# NumPy Histogram Specification

Port of np_histogram.dfy to Lean 4
-/

namespace DafnySpecs.NpHistogram

-- LLM HELPER
def find_bin {m : Nat} (value : Float) (bins : Vector Float m) : Int :=
  let rec find_bin_aux (i : Nat) : Int :=
    if i >= m - 1 then m - 2
    else if i == 0 then 0
    else if value >= bins[i]! && value < bins[i + 1]! then i
    else find_bin_aux (i + 1)
  find_bin_aux 0

-- LLM HELPER
def increment_bin {m : Nat} (hist : Vector Int m) (bin_index : Int) : Vector Int m :=
  if bin_index >= 0 && bin_index < m then
    Vector.ofFn (fun i => if i.val == bin_index.natAbs then hist[i]! + 1 else hist[i]!)
  else hist

/-- Compute histogram of data given bins -/
def histogram {n m : Nat} (data : Vector Float n) (bins : Vector Float m) : Vector Int (m - 1) :=
  let initial_hist := Vector.replicate (m - 1) (0 : Int)
  let rec process_data (i : Nat) (hist : Vector Int (m - 1)) : Vector Int (m - 1) :=
    if i >= n then hist
    else
      let value := data[i]!
      let bin_index := find_bin value bins
      let updated_hist := increment_bin hist bin_index
      process_data (i + 1) updated_hist
  process_data 0 initial_hist

/-- Helper function for histogram computation -/
def histogram_helper {n m : Nat} (data : Vector Float n) (bins : Vector Float m) (hist : Vector Int (m - 1)) (index : Int) : Vector Int (m - 1) :=
  if index >= n then hist
  else if index < 0 then hist
  else
    let value := data[index.natAbs]!
    let bin_index := find_bin value bins
    let updated_hist := increment_bin hist bin_index
    histogram_helper data bins updated_hist (index + 1)
termination_by (n - index.natAbs)
decreasing_by
  simp only [Int.natAbs_add_one]
  have h_pos : index >= 0 := by
    by_contra h_neg
    push_neg at h_neg
    simp at h_neg
    split_ifs at * with h_ge h_lt
    · exact absurd h_ge (Int.not_le.mpr h_neg)
    · contradiction
  have h_bound : index.natAbs < n := by
    rw [Int.natAbs_of_nonneg h_pos]
    split_ifs at * with h_ge h_lt
    · linarith
    · exact Nat.zero_le _
  simp [Nat.sub_sub, Int.natAbs_of_nonneg h_pos]
  have : index.natAbs + 1 - index.natAbs = 1 := by
    rw [Nat.add_sub_cancel]
  rw [this]
  have : index.natAbs < n := h_bound
  omega

/-- Specification: The result has correct length -/
theorem histogram_length {n m : Nat} (data : Vector Float n) (bins : Vector Float m)
  (h1 : m ≥ 2)
  (h2 : ∀ i : Fin (m - 1), bins[i.succ] > bins[i]) :
  let hist := histogram data bins
  hist.toList.length = m - 1 := by
  simp [histogram]
  exact Vector.toList_length

/-- Specification: Data length constraint -/
theorem histogram_data_constraint {n m : Nat} (_ : Vector Float n) (_ : Vector Float m)
  (_ : m ≥ 2) :
  n ≥ 0 := 
  Nat.zero_le n

end DafnySpecs.NpHistogram