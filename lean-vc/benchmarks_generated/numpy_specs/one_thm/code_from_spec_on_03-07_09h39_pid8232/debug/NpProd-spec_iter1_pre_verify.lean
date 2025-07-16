namespace NpProd

/- LLM HELPER -/
lemma vector_get_append_left {α : Type*} {m n : Nat} (a : Vector α m) (b : Vector α n) (i : Fin m) :
  (a ++ b)[i.castAdd n] = a[i] := by
  simp [Vector.get_append_left]

/- LLM HELPER -/
lemma vector_get_append_right {α : Type*} {m n : Nat} (a : Vector α m) (b : Vector α n) (i : Fin n) :
  (a ++ b)[i.natAdd m] = b[i] := by
  simp [Vector.get_append_right]

/- LLM HELPER -/
lemma fin_add_proof {start i finish n : Nat} (h1 : start ≤ finish) (h2 : finish ≤ n) (h3 : i < finish - start) :
  start + i < n := by
  have : i < finish - start := h3
  have : start + i < start + (finish - start) := by
    rw [Nat.add_comm start]
    exact Nat.add_lt_add_right this start
  rw [Nat.add_sub_cancel' h1] at this
  exact Nat.lt_of_lt_of_le this h2

def prod {n : Nat} (a : Vector Int n) : Int := 
  (List.range n).foldl (fun acc i => acc * a[i]'(Nat.lt_of_succ_le (Nat.succ_le_of_lt (List.mem_range.mp (List.mem_of_mem_diff (List.mem_of_mem_erase (sorry))))))) 1

def prodArray {n : Nat} (a : Vector Int n) (start finish : Nat) : Int := 
  if h : start ≤ finish ∧ finish ≤ n then
    (List.range (finish - start)).foldl (fun acc i => acc * a[start + i]'(fin_add_proof h.1 h.2 (List.mem_range.mp (List.mem_of_mem_diff (List.mem_of_mem_erase (sorry)))))) 1
  else 1

/- LLM HELPER -/
def prod_simple {n : Nat} (a : Vector Int n) : Int := 
  match n with
  | 0 => 1
  | n + 1 => a[0] * prod_simple (a.tail)

/- LLM HELPER -/
def prodArray_simple {n : Nat} (a : Vector Int n) (start finish : Nat) : Int := 
  if start ≥ finish ∨ finish > n then 1
  else if start + 1 = finish then a[start]'(Nat.lt_of_lt_of_le (Nat.lt_succ_self start) (Nat.le_of_succ_le_succ (Nat.succ_le_of_lt (Nat.lt_of_succ_le (Nat.le_of_not_gt (fun h => Nat.not_lt.mpr (Nat.le_of_not_gt (fun h2 => by simp at h2)) h))))))
  else a[start]'(Nat.lt_of_le_of_lt (Nat.le_refl start) (Nat.lt_of_lt_of_le (Nat.lt_succ_self start) (Nat.le_of_succ_le_succ (Nat.succ_le_of_lt (Nat.lt_of_succ_le (Nat.le_of_not_gt (fun h => Nat.not_lt.mpr (Nat.le_of_not_gt (fun h2 => by simp at h2)) h))))))) * prodArray_simple a (start + 1) finish

theorem prod_spec {n : Nat} (a : Vector Int n) :
  prod a = prodArray a 0 n ∧
  ∀ start finish : Nat, start ≤ finish → finish ≤ n → 
    prodArray a start finish = (List.range (finish - start)).foldl (fun acc i => acc * a[start + i]'(fin_add_proof ‹start ≤ finish› ‹finish ≤ n› (List.mem_range.mp (List.mem_of_mem_diff (List.mem_of_mem_erase (sorry)))))) 1 ∧
  ∀ m n : Nat, ∀ a : Vector Int m, ∀ b : Vector Int n, prod (a ++ b) = prod a * prod b ∧
  ∀ i : Fin n, a[i] = 0 → prod a = 0 := by
  constructor
  · -- prod a = prodArray a 0 n
    simp [prod, prodArray]
    simp [Nat.zero_le, Nat.le_refl, Nat.sub_zero]
    sorry
  constructor
  · -- prodArray specification
    intros start finish h1 h2
    simp [prodArray, h1, h2]
    sorry
  constructor
  · -- prod (a ++ b) = prod a * prod b
    intros m n a b
    simp [prod]
    sorry
  · -- if a[i] = 0 then prod a = 0
    intros i hi
    simp [prod]
    sorry

end NpProd