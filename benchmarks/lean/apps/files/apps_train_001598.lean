-- <vc-helpers>
-- </vc-helpers>

def string_func (s : String) (x : Nat) : String := sorry 

theorem string_func_length_preserving (s : String) (x : Nat) 
  (h : s.length ≥ 2) : 
  (string_func s x).length = s.length := sorry

theorem string_func_permutation (s : String) (x : Nat)
  (h : s.length ≥ 2) :
  ∃ (perm : List Char), perm.length = s.length ∧ 
  (string_func s x).toList = perm ∧
  ∀ c, c ∈ perm ↔ c ∈ s.toList := sorry

theorem string_func_iteration_consistency (s : String) (k : Nat)
  (h : s.length ≥ 2) :
  let iter := fun (s : String) => string_func s 1
  Nat.recOn k s (fun _ res => iter res) = string_func s k := sorry

theorem string_func_cycle (s : String)
  (h : s.length ≥ 2) :
  ∃ (n m : Nat), n > m ∧ 
  let iter := fun (s : String) => string_func s 1
  iter (iter s) = s := sorry

/-
info: 'nrtgSi'
-/
-- #guard_msgs in
-- #eval string_func "String" 3

/-
info: 'iitkIl !e '
-/
-- #guard_msgs in
-- #eval string_func "I like it!" 1234

/-
info: 'fonroisreinrddgdneyscou'
-/
-- #guard_msgs in
-- #eval string_func "codingisfornerdsyounerd" 10101010

-- Apps difficulty: interview
-- Assurance level: unguarded