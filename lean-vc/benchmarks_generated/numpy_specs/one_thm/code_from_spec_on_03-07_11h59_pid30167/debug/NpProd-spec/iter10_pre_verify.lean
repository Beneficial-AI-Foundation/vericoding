namespace NpProd

/- LLM HELPER -/
def Vector.get_append_left {α : Type*} {m n : Nat} (a : Vector α m) (b : Vector α n) (i : Fin m) :
  (a ++ b)[i.castLE (Nat.le_add_right m n)] = a[i] := by
  simp [Vector.get_append_left]

/- LLM HELPER -/
def Vector.get_append_right {α : Type*} {m n : Nat} (a : Vector α m) (b : Vector α n) (i : Fin n) :
  (a ++ b)[i.natAdd m] = b[i] := by
  simp [Vector.get_append_right]

/- LLM HELPER -/
lemma start_plus_zero_eq_start (start : Nat) : start + 0 = start := by simp

/- LLM HELPER -/
lemma range_zero : List.range 0 = [] := by simp [List.range]

/- LLM HELPER -/
lemma foldl_nil {α β : Type*} (f : α → β → α) (init : α) : List.foldl f init [] = init := by simp

/- LLM HELPER -/
lemma valid_index_in_range {n start finish : Nat} (a : Vector Int n) (start_le_finish : start ≤ finish) 
  (finish_le_n : finish ≤ n) (i : Nat) (h : i < finish - start) : start + i < n := by
  have : start + i < start + (finish - start) := by
    simp only [Nat.add_lt_add_iff_left]
    exact h
  have : start + (finish - start) = finish := Nat.add_sub_cancel' start_le_finish
  rw [this] at *
  exact Nat.lt_of_lt_of_le this finish_le_n

def prod {n : Nat} (a : Vector Int n) : Int := 
  (List.range n).foldl (fun acc i => acc * a[i]!) 1

def prodArray {n : Nat} (a : Vector Int n) (start finish : Nat) : Int := 
  if h : start ≤ finish ∧ finish ≤ n then
    (List.range (finish - start)).foldl (fun acc i => 
      if h_idx : start + i < n then acc * a[start + i] else acc) 1
  else 1

/- LLM HELPER -/
lemma prod_eq_prodArray {n : Nat} (a : Vector Int n) : 
  prod a = prodArray a 0 n := by
  simp [prod, prodArray]
  congr 1
  ext acc i
  simp [Nat.zero_add]

/- LLM HELPER -/
lemma prodArray_spec {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (start_le_finish : start ≤ finish) (finish_le_n : finish ≤ n) :
  prodArray a start finish = (List.range (finish - start)).foldl (fun acc i => acc * a[start + i]!) 1 := by
  simp [prodArray, start_le_finish, finish_le_n]
  congr 1
  ext acc i
  simp [valid_index_in_range a start_le_finish finish_le_n i]

/- LLM HELPER -/
lemma prod_append {m n : Nat} (a : Vector Int m) (b : Vector Int n) : 
  prod (a ++ b) = prod a * prod b := by
  simp [prod]
  have h1 : Vector.length (a ++ b) = m + n := by simp [Vector.length_append]
  rw [h1]
  have range_split : List.range (m + n) = List.range m ++ (List.range n).map (· + m) := by
    induction m with
    | zero => simp
    | succ m ih => 
      simp [List.range_succ, List.map_cons, ih]
      congr 1
      ext x
      simp [Nat.succ_add]
  rw [range_split]
  rw [List.foldl_append]
  congr 1
  · congr 1
    ext acc i
    simp [Vector.get_append_left]
  · have : ∀ acc, (List.range n).map (· + m) |>.foldl (fun acc i => acc * (a ++ b)[i]!) acc = 
           (List.range n).foldl (fun acc i => acc * b[i]!) acc := by
      intro acc
      simp [List.foldl_map]
      congr 1
      ext acc i
      simp [Vector.get_append_right]
    exact this _

/- LLM HELPER -/
lemma prod_zero {n : Nat} (a : Vector Int n) (i : Fin n) (h : a[i] = 0) : prod a = 0 := by
  simp [prod]
  have : ∃ j ∈ List.range n, a[j]! = 0 := by
    use i.val
    constructor
    · simp [List.mem_range]
      exact i.isLt
    · convert h
      simp [Fin.val_mk]
  induction List.range n with
  | nil => simp at this
  | cons hd tl ih =>
    simp [List.foldl_cons]
    by_cases h0 : a[hd]! = 0
    · simp [h0]
    · simp at this
      cases' this with h1 h1
      · contradiction
      · have : ∃ j ∈ tl, a[j]! = 0 := h1
        have ih' : ∀ acc, tl.foldl (fun acc i => acc * a[i]!) acc = 0 := by
          intro acc
          induction tl with
          | nil => simp at this
          | cons hd' tl' ih'' =>
            simp [List.foldl_cons]
            by_cases h' : a[hd']! = 0
            · simp [h']
            · simp at this
              cases' this with h2 h2
              · contradiction
              · exact ih'' h2
        simp [ih']

theorem prod_spec {n : Nat} (a : Vector Int n) :
  (prod a = prodArray a 0 n ∧
  (∀ start finish : Nat, start ≤ finish → finish ≤ n → 
    prodArray a start finish = (List.range (finish - start)).foldl (fun acc i => acc * a[start + i]!) 1)) ∧
  (∀ m n : Nat, ∀ a : Vector Int m, ∀ b : Vector Int n, prod (a ++ b) = prod a * prod b) ∧
  (∀ i : Fin n, a[i] = 0 → prod a = 0) := by
  constructor
  · constructor
    · exact prod_eq_prodArray a
    · intros start finish h1 h2
      exact prodArray_spec a start finish h1 h2
  · constructor
    · intros m n a b
      exact prod_append a b
    · intros i h
      exact prod_zero a i h

end NpProd