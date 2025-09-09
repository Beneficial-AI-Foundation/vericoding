def sub (a b : List α) : Bool := sorry

def sub_string (a b : String) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

def subword (t : List Int) (ord_ar : List Int) (n : Int) : List Int := sorry

def bin_s (l r : Int) (f : Int → Bool) : Int := sorry

@[simp] theorem sub_empty (a : List α) : 
  sub a [] = true := sorry

@[simp] theorem sub_longer (a s : List α) :
  List.length s > List.length a → sub a s = false := sorry

@[simp] theorem sub_refl (a : List α) :
  sub a a = true := sorry

@[simp] theorem sub_string_empty (a b : String) :
  sub_string a "" = true := sorry

@[simp] theorem sub_string_longer (a b : String) :
  String.length b > String.length a → sub_string a b = false := sorry

@[simp] theorem sub_string_refl (a : String) :
  sub_string a a = true := sorry

theorem subword_length (t : List Int) (ord_ar : List Int) (n : Int) :
  List.length t = List.length ord_ar → 
  List.length (subword t ord_ar n) ≤ List.length t := sorry

theorem bin_search_bounds (l r : Int) (f : Int → Bool) :
  r > l + 1 →
  let res := bin_s l r f
  l ≤ res ∧ res ≤ r := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve "ababcba" "abb" [5, 3, 4, 1, 7, 6, 2]

/-
info: 4
-/
-- #guard_msgs in
-- #eval solve "bbbabb" "bb" [1, 6, 3, 4, 2, 5]

/-
info: 9
-/
-- #guard_msgs in
-- #eval solve "cacaccccccacccc" "cacc" [10, 9, 14, 5, 1, 7, 15, 3, 6, 12, 4, 8, 11, 13, 2]

-- Apps difficulty: competition
-- Assurance level: guarded