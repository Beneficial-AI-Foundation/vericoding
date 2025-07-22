/-
# NumPy Histogram Specification

Port of np_histogram.dfy to Lean 4
-/

namespace DafnySpecs.NpHistogram

-- LLM HELPER
def find_bin {m : Nat} (value : Float) (bins : Vector Float m) : Int :=
  let rec find_bin_aux (i : Nat) : Int :=
    if i >= m - 1 then Int.ofNat (m - 2)
    else if i = 0 then 
      if value < bins[i]! then Int.ofNat i
      else find_bin_aux (i + 1)
    else if i < m - 1 then
      if value >= bins[i]! && value < bins[i + 1]! then Int.ofNat i
      else find_bin_aux (i + 1)
    else Int.ofNat (m - 2)
  if m ≤ 1 then -1 else find_bin_aux 0

-- LLM HELPER
def increment_bin {m : Nat} (hist : Vector Int m) (bin_idx : Int) : Vector Int m :=
  if bin_idx < 0 || bin_idx >= Int.ofNat m then hist
  else
    let idx := Int.natAbs bin_idx
    if h : idx < m then
      hist.set ⟨idx, h⟩ (hist[idx]! + 1)
    else hist

/-- Helper function for histogram computation -/
def histogram_helper {n m : Nat} (data : Vector Float n) (bins : Vector Float m) (hist : Vector Int (m - 1)) (index : Int) : Vector Int (m - 1) :=
  if index < 0 || index >= Int.ofNat n then hist
  else
    let data_idx := Int.natAbs index
    if h : data_idx < n then
      let value := data[data_idx]!
      let bin_idx := find_bin value bins
      let new_hist := increment_bin hist bin_idx
      histogram_helper data bins new_hist (index + 1)
    else hist

/-- Compute histogram of data given bins -/
def histogram {n m : Nat} (data : Vector Float n) (bins : Vector Float m) : Vector Int (m - 1) :=
  let initial_hist := Vector.replicate (m - 1) 0
  histogram_helper data bins initial_hist 0

/-- Specification: The result has correct length -/
theorem histogram_length {n m : Nat} (data : Vector Float n) (bins : Vector Float m)
  (h1 : m ≥ 2)
  (h2 : ∀ i : Fin (m - 1), bins[i.succ.val]! > bins[i.val]!) :
  let hist := histogram data bins
  hist.toList.length = m - 1 := by
  simp [histogram]
  simp [Vector.toList_length]

/-- Specification: Data length constraint -/
theorem histogram_data_constraint {n m : Nat} (data : Vector Float n) (bins : Vector Float m)
  (h1 : m ≥ 2)
  (h2 : ∀ i : Fin (m - 1), bins[i.succ.val]! > bins[i.val]!) :
  n ≥ 0 := by
  exact Nat.zero_le n

end DafnySpecs.NpHistogram