namespace NpProd

def prod {n : Nat} (a : Vector Int n) : Int := 
  a.toList.foldl (· * ·) 1

-- LLM HELPER
def prodArrayHelper (lst : List Int) (start finish : Nat) : Int :=
  if start ≥ finish then 1
  else (lst.drop start).take (finish - start) |>.foldl (· * ·) 1

def prodArray {n : Nat} (a : Vector Int n) (start finish : Nat) : Int := 
  if start ≥ finish ∨ finish > n then 1
  else prodArrayHelper a.toList start finish

-- LLM HELPER
lemma vector_get_eq_list_get {n : Nat} (a : Vector Int n) (i : Fin n) :
  a[i] = a.toList.get ⟨i.val, by simp [Vector.toList_length]; exact i.isLt⟩ := by
  simp [Vector.get_eq_get]

-- LLM HELPER
lemma list_range_foldl_eq_drop_take {lst : List Int} (start finish : Nat) :
  start ≤ finish → finish ≤ lst.length →
  (List.range (finish - start)).foldl (fun acc i => acc * lst.get ⟨start + i, by
    have h1 : i < finish - start := List.mem_range.mp (List.get_mem _ _ _)
    omega
  ⟩) 1 = (lst.drop start).take (finish - start) |>.foldl (· * ·) 1 := by
  intro h1 h2
  have : finish - start ≤ lst.length - start := by omega
  clear h1 h2
  generalize hk : finish - start = k
  clear finish hk
  induction k generalizing start lst with
  | zero => simp [List.range_zero]
  | succ k ih =>
    simp [List.range_succ, List.foldl_cons]
    rw [← ih]
    simp [List.drop_succ_cons]
    sorry

-- LLM HELPER
lemma prod_append {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  prod (a ++ b) = prod a * prod b := by
  simp [prod, Vector.append_toList, List.foldl_append]

-- LLM HELPER
lemma prod_zero {n : Nat} (a : Vector Int n) (i : Fin n) :
  a[i] = 0 → prod a = 0 := by
  intro h
  simp [prod]
  have : 0 ∈ a.toList := by
    rw [Vector.mem_toList_iff]
    use i
    exact h
  exact List.foldl_mul_zero_mem this

theorem prod_spec {n : Nat} (a : Vector Int n) :
  prod a = prodArray a 0 n ∧
  ∀ start finish : Nat, start ≤ finish → finish ≤ n → 
    prodArray a start finish = (List.range (finish - start)).foldl (fun acc i => acc * a[start + i]'(by
      have h1 : i < finish - start := List.mem_range.mp (List.get_mem _ _ _)
      omega
    )) 1 ∧
  ∀ m n : Nat, ∀ a : Vector Int m, ∀ b : Vector Int n, prod (a ++ b) = prod a * prod b ∧
  ∀ i : Fin n, a[i] = 0 → prod a = 0 := by
  constructor
  · simp [prod, prodArray, prodArrayHelper]
    simp [Vector.toList_length, List.drop_zero, List.take_length]
  constructor
  · intro start finish h1 h2
    simp [prodArray]
    split_ifs with h
    · simp at h
      cases h with
      | inl h => omega
      | inr h => omega
    · simp [prodArrayHelper]
      sorry
  constructor
  · intro m n a b
    exact prod_append a b
  · intro i h
    exact prod_zero a i h

end NpProd