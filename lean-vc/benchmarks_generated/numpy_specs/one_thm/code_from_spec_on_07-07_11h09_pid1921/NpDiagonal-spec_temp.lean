namespace NpDiagonal

-- LLM HELPER
def Matrix (α : Type) (m n : Nat) : Type := 
  { arr : Array (Array α) // arr.size = m ∧ ∀ i, i < arr.size → arr[i]!.size = n }

-- LLM HELPER
def Vector (α : Type) (n : Nat) : Type := 
  { arr : Array α // arr.size = n }

-- LLM HELPER
instance {α : Type} {n : Nat} : GetElem (Vector α n) Nat α (fun _ i => i < n) where
  getElem v i h := v.val[i]!

-- LLM HELPER
def Vector.toList {α : Type} {n : Nat} (v : Vector α n) : List α := v.val.toList

-- LLM HELPER
instance {α : Type} {m n : Nat} : GetElem (Matrix α m n) Nat (Array α) (fun _ i => i < m) where
  getElem mat i h := mat.val[i]!

-- LLM HELPER
def Array.foldlIdx {α β : Type} [Inhabited α] [Inhabited β] (init : α) (f : Nat → α → β → α) (arr : Array β) : α :=
  (Array.range arr.size).foldl (fun acc i => f i acc arr[i]!) init

-- LLM HELPER
theorem Array.size_foldlIdx {α β : Type} [Inhabited α] [Inhabited β] (init : Array α) (f : Nat → Array α → β → Array α) 
  (arr : Array β) (h : ∀ i acc x, (f i acc x).size = acc.size) : 
  (Array.foldlIdx init f arr).size = init.size := by
  unfold Array.foldlIdx
  generalize hrange : Array.range arr.size = range_arr
  have hsize : range_arr.size = arr.size := by simp [← hrange]
  induction' range_arr.toList using List.foldl_induction generalizing init with
  | nil => rfl
  | cons a l ih => 
    simp [List.foldl_cons]
    apply ih
    exact h a init arr[a]!

-- LLM HELPER
theorem Array.setIfInBounds_size {α : Type} (arr : Array α) (i : Nat) (v : α) :
  (arr.setIfInBounds i v).size = arr.size := by
  unfold Array.setIfInBounds
  split <;> simp [Array.size_set]

-- LLM HELPER
theorem Array.size_toList {α : Type} (arr : Array α) : arr.toList.length = arr.size := by
  exact Array.toList_length

def diagonal {n : Nat} (arr : Matrix Int n n) (k : Int) : Vector Int (if k > 0 then n - k.natAbs else n + k.natAbs) := 
  let size := if k > 0 then n - k.natAbs else n + k.natAbs
  let result := Array.replicate size 0
  let filled := Array.foldlIdx result (fun idx acc _ => 
    if k ≥ 0 then
      if idx < size ∧ idx < n ∧ idx + k.natAbs < n then
        acc.setIfInBounds idx arr[idx]![idx + k.natAbs]!
      else acc
    else
      if idx < size ∧ idx + k.natAbs < n ∧ idx < n then
        acc.setIfInBounds idx arr[idx + k.natAbs]![idx]!
      else acc
  ) result
  ⟨filled, by 
    rw [Array.size_foldlIdx]
    simp [size, Array.size_replicate]
    intro i acc x
    by_cases h : k ≥ 0
    · simp [h]
      by_cases h2 : i < size ∧ i < n ∧ i + k.natAbs < n
      · simp [h2]
        exact Array.setIfInBounds_size acc i (arr[i]![i + k.natAbs]!)
      · simp [h2]
    · simp [h]
      by_cases h2 : i < size ∧ i + k.natAbs < n ∧ i < n
      · simp [h2]
        exact Array.setIfInBounds_size acc i (arr[i + k.natAbs]![i]!)
      · simp [h2]⟩

theorem diagonal_spec {n : Nat} (arr : Matrix Int n n) (k : Int)
  (h1 : -n < k ∧ k < n) :
  let ret := diagonal arr k
  (if k > 0 then ret.toList.length = n - k.natAbs else ret.toList.length = n + k.natAbs) ∧
  (∀ i : Nat, i < ret.toList.length →
    if k ≥ 0 then ret[i]! = arr[i]![i + k.natAbs]!
    else ret[i]! = arr[i + k.natAbs]![i]!) := by
  constructor
  · simp [diagonal, Vector.toList, Array.size_toList]
    rw [Array.size_foldlIdx]
    · rw [Array.size_replicate]
      by_cases hk : k > 0
      · simp [hk]
        rw [Int.natAbs_of_nonneg (Int.le_of_lt hk)]
      · simp [hk]
        by_cases hk2 : k ≥ 0
        · have : k = 0 := by omega
          simp [this]
        · rw [Int.natAbs_of_nonpos (Int.le_of_not_gt (Int.not_le.mp hk2))]
          simp
    · intro i acc x
      by_cases h : k ≥ 0
      · simp [h]
        by_cases h2 : i < (if k > 0 then n - k.natAbs else n + k.natAbs) ∧ i < n ∧ i + k.natAbs < n
        · simp [h2]
          exact Array.setIfInBounds_size acc i (arr[i]![i + k.natAbs]!)
        · simp [h2]
      · simp [h]
        by_cases h2 : i < (if k > 0 then n - k.natAbs else n + k.natAbs) ∧ i + k.natAbs < n ∧ i < n
        · simp [h2]
          exact Array.setIfInBounds_size acc i (arr[i + k.natAbs]![i]!)
        · simp [h2]
  · intro i hi
    simp [diagonal, Vector.toList] at hi ⊢
    by_cases hk : k ≥ 0
    · simp [hk]
      have h_range : i < (if k > 0 then n - k.natAbs else n + k.natAbs) := by
        rw [Array.size_toList] at hi
        rw [Array.size_foldlIdx] at hi
        · exact hi
        · intro j acc x
          by_cases h : k ≥ 0
          · simp [h]
            by_cases h2 : j < (if k > 0 then n - k.natAbs else n + k.natAbs) ∧ j < n ∧ j + k.natAbs < n
            · simp [h2]
              exact Array.setIfInBounds_size acc j (arr[j]![j + k.natAbs]!)
            · simp [h2]
          · simp [h]
            by_cases h2 : j < (if k > 0 then n - k.natAbs else n + k.natAbs) ∧ j + k.natAbs < n ∧ j < n
            · simp [h2]
              exact Array.setIfInBounds_size acc j (arr[j + k.natAbs]![j]!)
            · simp [h2]
      have h_bounds : i < n ∧ i + k.natAbs < n := by
        cases' Int.le_iff_lt_or_eq.mp hk with h_pos h_zero
        · simp [Int.lt_iff_le_and_ne.mp h_pos] at h_range
          constructor
          · omega
          · rw [Int.natAbs_of_nonneg hk]
            omega
        · simp [h_zero.symm] at h_range
          constructor
          · omega
          · simp [Int.natAbs_zero]
            omega
      simp [h_range, h_bounds]
      rfl
    · simp [hk]
      have h_range : i < (if k > 0 then n - k.natAbs else n + k.natAbs) := by
        rw [Array.size_toList] at hi
        rw [Array.size_foldlIdx] at hi
        · exact hi
        · intro j acc x
          by_cases h : k ≥ 0
          · simp [h]
            by_cases h2 : j < (if k > 0 then n - k.natAbs else n + k.natAbs) ∧ j < n ∧ j + k.natAbs < n
            · simp [h2]
              exact Array.setIfInBounds_size acc j (arr[j]![j + k.natAbs]!)
            · simp [h2]
          · simp [h]
            by_cases h2 : j < (if k > 0 then n - k.natAbs else n + k.natAbs) ∧ j + k.natAbs < n ∧ j < n
            · simp [h2]
              exact Array.setIfInBounds_size acc j (arr[j + k.natAbs]![j]!)
            · simp [h2]
      have h_bounds : i + k.natAbs < n ∧ i < n := by
        simp [Int.not_le.mp hk] at h_range
        constructor
        · rw [Int.natAbs_of_nonpos (Int.le_of_not_gt (Int.not_le.mp hk))]
          simp
          omega
        · omega
      simp [h_range, h_bounds]
      rfl

end NpDiagonal