namespace NpHistogram

-- LLM HELPER
def find_bin_index {m : Nat} (value : Float) (bins : Vector Float m) : Int :=
  let rec find_bin_aux (i : Nat) : Int :=
    if i + 1 >= m then Int.ofNat (m - 2)
    else if value < bins[i + 1]! then Int.ofNat i
    else find_bin_aux (i + 1)
  if m ≤ 1 then -1
  else if value < bins[0]! then -1
  else if value >= bins[m - 1]! then -1
  else find_bin_aux 0

-- LLM HELPER
def increment_at {k : Nat} (vec : Vector Int k) (index : Int) : Vector Int k :=
  if index < 0 ∨ index >= Int.ofNat k then vec
  else
    let nat_index := Int.natAbs index
    if nat_index < k then
      Vector.ofFn (fun i => if i.val = nat_index then vec[i] + 1 else vec[i])
    else vec

def histogram_helper {n m : Nat} (data : Vector Float n) (bins : Vector Float m) (hist : Vector Int (m - 1)) (index : Int) : Vector Int (m - 1) :=
  if index < 0 ∨ index >= Int.ofNat n then hist
  else
    let nat_index := Int.natAbs index
    if nat_index < n then
      let value := data[nat_index]!
      let bin_idx := find_bin_index value bins
      let new_hist := increment_at hist bin_idx
      histogram_helper data bins new_hist (index + 1)
    else hist
termination_by Int.ofNat n - index

def histogram {n m : Nat} (data : Vector Float n) (bins : Vector Float m) : Vector Int (m - 1) :=
  let empty_hist := Vector.replicate (m - 1) 0
  histogram_helper data bins empty_hist 0

-- LLM HELPER
lemma vector_length_preserved {k : Nat} (vec : Vector Int k) : vec.toList.length = k := by
  simp [Vector.toList_length]

theorem histogram_spec {n m : Nat} (data : Vector Float n) (bins : Vector Float m)
  (h1 : m ≥ 2)
  (h2 : ∀ i : Fin (m - 1), bins[i.succ] > bins[i]) :
  let hist := histogram data bins
  (hist.toList.length = m - 1) ∧
  (n ≥ 0) := by
  constructor
  · simp [histogram]
    apply vector_length_preserved
  · exact Nat.zero_le n

end NpHistogram