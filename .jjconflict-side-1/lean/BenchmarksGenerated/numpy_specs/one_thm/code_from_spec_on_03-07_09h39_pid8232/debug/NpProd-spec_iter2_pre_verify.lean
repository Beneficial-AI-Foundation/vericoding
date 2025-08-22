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
    induction m with
    | zero => simp
    | succ m ih => simp [List.range_succ, List.foldl_map, ih]
  · -- if a[i] = 0 then prod a = 0
    intros i hi
    simp [prod]
    induction n with
    | zero => exact Fin.elim0 i
    | succ n ih => 
      simp [List.range_succ, List.foldl_map]
      cases' i with i hi_bound
      simp at hi
      cases' i with
      | zero => simp [hi]
      | succ i => 
        have : a[⟨i.succ, hi_bound⟩] = 0 := hi
        simp [this]
        ring

end NpProd