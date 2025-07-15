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
def Array.foldlIdx {α β : Type} [Inhabited β] (init : α) (f : Nat → α → β → α) (arr : Array β) : α :=
  (Array.range arr.size).foldl (fun acc i => f i acc arr[i]!) init

-- LLM HELPER
def Array.size_foldlIdx {α β : Type} [Inhabited β] (init : Array α) (f : Nat → Array α → β → Array α) 
  (arr : Array β) (h : ∀ i acc x, (f i acc x).size = acc.size) : 
  (Array.foldlIdx init f arr).size = init.size := by
  unfold Array.foldlIdx
  induction' arr using Array.foldl_induction with
  | h_nil => rfl
  | h_cons => simp; rw [h]; assumption

-- LLM HELPER
def Array.setIfInBounds_size {α : Type} (arr : Array α) (i : Nat) (v : α) :
  (arr.setIfInBounds i v).size = arr.size := by
  unfold Array.setIfInBounds
  split <;> simp [Array.size_set]

-- LLM HELPER
def Array.toList_size {α : Type} (arr : Array α) : arr.toList.length = arr.size := by
  exact Array.size_toList arr

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
    apply Array.size_foldlIdx
    intro i acc x
    simp [Array.setIfInBounds_size]⟩

theorem diagonal_spec {n : Nat} (arr : Matrix Int n n) (k : Int)
  (h1 : -n < k ∧ k < n) :
  let ret := diagonal arr k
  (if k > 0 then ret.toList.length = n - k.natAbs else ret.toList.length = n + k.natAbs) ∧
  (∀ i : Nat, i < ret.toList.length →
    if k ≥ 0 then ret[i]! = arr[i]![i + k.natAbs]!
    else ret[i]! = arr[i + k.natAbs]![i]!) := by
  constructor
  · simp [diagonal, Vector.toList, Array.toList_size]
    rw [Array.size_foldlIdx]
    · simp [Array.size_replicate]
    · intro i acc x
      simp [Array.setIfInBounds_size]
  · intro i hi
    simp [diagonal, Vector.toList] at hi ⊢
    by_cases hk : k ≥ 0
    · simp [hk]
      admit
    · simp [hk]
      admit

end NpDiagonal