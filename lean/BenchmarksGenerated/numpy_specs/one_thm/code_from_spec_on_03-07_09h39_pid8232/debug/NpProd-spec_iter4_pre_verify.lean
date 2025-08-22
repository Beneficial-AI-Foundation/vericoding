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
  (List.range n).foldl (fun acc i => acc * a[i]!) 1

def prodArray {n : Nat} (a : Vector Int n) (start finish : Nat) : Int := 
  if h : start ≤ finish ∧ finish ≤ n then
    (List.range (finish - start)).foldl (fun acc i => acc * a[start + i]!) 1
  else 1

/- LLM HELPER -/
def prod_simple {n : Nat} (a : Vector Int n) : Int := 
  match n with
  | 0 => 1
  | n + 1 => a[0] * prod_simple (a.tail)

/- LLM HELPER -/
def prodArray_simple {n : Nat} (a : Vector Int n) (start finish : Nat) : Int := 
  if start ≥ finish ∨ finish > n then 1
  else if start + 1 = finish then a[start]!
  else a[start]! * prodArray_simple a (start + 1) finish
  termination_by (finish - start)

/- LLM HELPER -/
lemma list_foldl_eq_zero_of_zero_mem {α : Type*} [Mul α] [Zero α] (f : α → Nat → α) (l : List Nat) (a : Nat → α) :
  (∃ i ∈ l, a i = 0) → (l.foldl (fun acc i => acc * a i) 1 = 0) := by
  intro h
  induction l with
  | nil => 
    simp at h
  | cons head tail ih =>
    simp at h
    cases h with
    | inl h1 => 
      simp [List.foldl_cons, h1]
      ring
    | inr h2 =>
      simp [List.foldl_cons]
      exact ih h2

theorem prod_spec {n : Nat} (a : Vector Int n) :
  prod a = prodArray a 0 n ∧
  ∀ start finish : Nat, start ≤ finish → finish ≤ n → 
    prodArray a start finish = (List.range (finish - start)).foldl (fun acc i => acc * a[start + i]!) 1 ∧
  ∀ m n : Nat, ∀ a : Vector Int m, ∀ b : Vector Int n, prod (a ++ b) = prod a * prod b ∧
  ∀ i : Fin n, a[i] = 0 → prod a = 0 := by
  constructor
  · -- prod a = prodArray a 0 n
    simp [prod, prodArray]
    simp [Nat.zero_le, Nat.le_refl, Nat.sub_zero]
  constructor
  · -- prodArray specification
    intros start finish h1 h2
    simp [prodArray, h1, h2]
  constructor
  · -- prod (a ++ b) = prod a * prod b
    intros m n a b
    simp [prod]
    have h : (List.range (m + n)).foldl (fun acc i => acc * (a ++ b)[i]!) 1 = 
             (List.range m).foldl (fun acc i => acc * a[i]!) 1 * 
             (List.range n).foldl (fun acc i => acc * b[i]!) 1 := by
      rw [List.range_add, List.foldl_append]
      simp [List.foldl_map]
      congr 1
      ext i
      simp [Vector.get_append_right]
    exact h
  · -- if a[i] = 0 then prod a = 0
    intros i hi
    simp [prod]
    have h : ∃ j ∈ List.range n, a[j]! = 0 := by
      use i.val
      constructor
      · exact List.mem_range.mpr i.isLt
      · exact hi
    exact list_foldl_eq_zero_of_zero_mem (fun acc i => acc * a[i]!) (List.range n) (fun i => a[i]!) h

end NpProd