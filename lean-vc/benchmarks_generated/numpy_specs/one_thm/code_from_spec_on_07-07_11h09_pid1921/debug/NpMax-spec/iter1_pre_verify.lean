namespace NpMax

-- LLM HELPER
def max_aux (a : Vector Int n) (acc : Int) (acc_idx : Fin n) (i : Fin n) : Int × Fin n :=
  if a[i] > acc then (a[i], i) else (acc, acc_idx)

-- LLM HELPER
def find_max_helper (a : Vector Int n) (start : Fin n) : Int × Fin n :=
  match n with
  | 0 => (0, start) -- This case won't occur due to h : n > 0
  | k + 1 => 
    let rec loop (i : Fin n) (acc : Int) (acc_idx : Fin n) : Int × Fin n :=
      if i.val = n - 1 then
        if a[i] > acc then (a[i], i) else (acc, acc_idx)
      else
        let new_acc := if a[i] > acc then a[i] else acc
        let new_idx := if a[i] > acc then i else acc_idx
        loop ⟨i.val + 1, Nat.lt_of_succ_lt_succ (Nat.succ_lt_succ i.isLt)⟩ new_acc new_idx
    loop start a[start] start

def max {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  let first_idx : Fin n := ⟨0, h⟩
  (find_max_helper a first_idx).1

-- LLM HELPER
lemma vector_nonempty_has_first {n : Nat} (h : n > 0) : ∃ i : Fin n, True := by
  use ⟨0, h⟩
  trivial

-- LLM HELPER
lemma max_is_element {n : Nat} (h : n > 0) (a : Vector Int n) : 
  ∃ i : Fin n, max h a = a[i] := by
  sorry

-- LLM HELPER  
lemma max_is_maximal {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∀ i : Fin n, a[i] ≤ max h a := by
  sorry

theorem max_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, max h a = a[i] ∧
  ∀ i : Fin n, a[i] ≤ max h a := by
  constructor
  · exact max_is_element h a
  · exact max_is_maximal h a

end NpMax