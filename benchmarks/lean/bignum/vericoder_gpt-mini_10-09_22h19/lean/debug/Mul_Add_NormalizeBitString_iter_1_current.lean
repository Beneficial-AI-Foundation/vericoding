namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Add (s1 s2 : String) : String :=
  sorry

axiom Add_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Add s1 s2) ∧ Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2

def NormalizeBitString (s : String) : String :=
  sorry

axiom NormalizeBitString_spec (s : String) :
  ValidBitString (NormalizeBitString s) ∧
  (NormalizeBitString s).length > 0 ∧
  ((NormalizeBitString s).length > 1 → (NormalizeBitString s).get? 0 = some '1') ∧
  (ValidBitString s → Str2Int s = Str2Int (NormalizeBitString s))

-- <vc-helpers>
-- LLM HELPER
theorem zero_valid : ValidBitString "0" := by
  intro i c h
  -- "0".get? 0 = some '0', otherwise none
  cases i <;> simp [String.get?] at h
  · injection h with h1; subst h1; simp
  · contradiction

-- LLM HELPER
theorem str2int_zero : Str2Int "0" = 0 := by
  dsimp [Str2Int]
  -- "0".data = ['0']
  have : "0".data = ['0'] := rfl
  rw [this]
  simp [List.foldl]

-- LLM HELPER
theorem push_zero_valid {s : String} (h : ValidBitString s) : ValidBitString (s.push '0') := by
  intro i c hi
  -- (s.push '0').get? i is either some char from s or the appended '0'
  -- Simplify by cases on i
  have : (s.push '0').get? i = 
    if i < s.length then s.get? i else if i = s.length then some '0' else none := by
    -- This equality is definitional in core String; use rfl
    rfl
  rw [this] at hi
  by_cases hi1 : i < s.length
  · rw [if_pos hi1] at hi
    exact h hi
  · have hi2 : i = s.length ∨ ¬ (i = s.length) := Or.em (i = s.length)
    cases hi2
    · rw [if_neg hi1, if_pos hi2] at hi
      injection hi with hc; subst hc; simp
    · rw [if_neg hi1, if_neg hi2] at hi
      contradiction

-- LLM HELPER
theorem str2int_push_zero {s : String} (h : ValidBitString s) : Str2Int (s.push '0') = 2 * Str2Int s := by
  dsimp [Str2Int]
  -- (s.push '0').data = s.data ++ ['0']
  have : (s.push '0').data = s.data ++ ['0'] := rfl
  rw [this]
  -- foldl over append: foldl f 0 (s.data ++ ['0']) = f (foldl f 0 s.data) '0'
  let f := fun (acc : Nat) (ch : Char) => 2 * acc + (if ch = '1' then 1 else 0)
  have : List.foldl f 0 (s.data ++ ['0']) = f (List.foldl f 0 s.data) '0' := by
    simp [List.foldl_append]
  rw [this]
  simp [f]; split_ifs <;> simp

-- LLM HELPER
theorem str2int_singleton (c : Char) : Str2Int (String.singleton c) = (if c = '1' then 1 else 0) := by
  dsimp [Str2Int]
  have : (String.singleton c).data = [c] := rfl
  rw [this]
  simp [List.foldl]

-- LLM HELPER
theorem rev_fold_bits_eq_str2int (s : String) :
  let l := s.data.reverse
  let g := fun (p : Nat × Nat) (ch : Char) => (p.1 + (if ch = '1' then p.2 else 0), 2 * p.2)
  (l.foldl g (0,1)).1 = Str2Int s := by
  -- Prove by induction on s.data
  let xs := s.data
  induction xs with
  | nil =>
    dsimp [rev_fold_bits_eq_str2int]; dsimp [Str2Int]
    -- empty string -> both sides 0
    simp
  | cons y ys ih =>
    dsimp [rev_fold_bits_eq_str2int]
    let l := (y :: ys).reverse
    -- (y :: ys).reverse = ys.reverse ++ [y]
    have : l = ys.reverse ++ [y] := by simp [l]
    rw [this]
    let g := fun (p : Nat × Nat) (ch : Char) => (p.1 + (if ch = '1' then p.2 else 0), 2 * p.2)
    -- foldl g (ys.reverse ++ [y]) (0,1) = fold over ys.reverse then over [y]
    have : (l.foldl g (0,1)).1 = ((ys.reverse).foldl g (0,1) |> fun p => (p.1 + (if y = '1' then p.2 else 0), 2 * p.2)).1 := by
      simp [List.foldl_append]
    rw [this]
    dsimp
    -- use induction hypothesis for ys
    have ih' := ih
    -- ih states: (ys.reverse.foldl g (0,1)).1 = Str2Int (String.mk (y :: ys)) without y? need to relate
    -- Build the string s = String.mk (y :: ys)
    let s' := String.mk (y :: ys)
    -- Apply ih to ys to get for s' without its head? We need relation between Str2Int s' and fold over ys.reverse
    -- Use direct computation:
    dsimp [Str2Int]
    -- compute Str2Int (String.mk (y :: ys)) = foldl f 0 (y :: ys) with f acc ch = 2*acc + (if ch='1' then 1 else 0)
    let f := fun (acc : Nat) (ch : Char) => 2 * acc + (if ch = '1' then 1 else 0)
    have : Str2Int (String.mk (y :: ys)) = List.foldl f 0 (y :: ys) := rfl
    rw [this]
    -- compute foldl f 0 (y :: ys) = f (List.foldl f 0 ys) y
    have : List.foldl f 0 (y :: ys) = f (List.foldl f 0 ys) y := by simp [List.foldl]
    rw [this]
    -- Now expand f
    simp [f]
    -- Now transform
-- </vc-helpers>

-- <vc-spec>
def Mul (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
theorem zero_valid : ValidBitString "0" := by
  intro i c h
  -- "0".get? 0 = some '0', otherwise none
  cases i <;> simp [String.get?] at h
  · injection h with h1; subst h1; simp
  · contradiction

-- LLM HELPER
theorem str2int_zero : Str2Int "0" = 0 := by
  dsimp [Str2Int]
  -- "0".data = ['0']
  have : "0".data = ['0'] := rfl
  rw [this]
  simp [List.foldl]

-- LLM HELPER
theorem push_zero_valid {s : String} (h : ValidBitString s) : ValidBitString (s.push '0') := by
  intro i c hi
  -- (s.push '0').get? i is either some char from s or the appended '0'
  -- Simplify by cases on i
  have : (s.push '0').get? i = 
    if i < s.length then s.get? i else if i = s.length then some '0' else none := by
    -- This equality is definitional in core String; use rfl
    rfl
  rw [this] at hi
  by_cases hi1 : i < s.length
  · rw [if_pos hi1] at hi
    exact h hi
  · have hi2 : i = s.length ∨ ¬ (i = s.length) := Or.em (i = s.length)
    cases hi2
    · rw [if_neg hi1, if_pos hi2] at hi
      injection hi with hc; subst hc; simp
    · rw [if_neg hi1, if_neg hi2] at hi
      contradiction

-- LLM HELPER
theorem str2int_push_zero {s : String} (h : ValidBitString s) : Str2Int (s.push '0') = 2 * Str2Int s := by
  dsimp [Str2Int]
  -- (s.push '0').data = s.data ++ ['0']
  have : (s.push '0').data = s.data ++ ['0'] := rfl
  rw [this]
  -- foldl over append: foldl f 0 (s.data ++ ['0']) = f (foldl f 0 s.data) '0'
  let f := fun (acc : Nat) (ch : Char) => 2 * acc + (if ch = '1' then 1 else 0)
  have : List.foldl f 0 (s.data ++ ['0']) = f (List.foldl f 0 s.data) '0' := by
    simp [List.foldl_append]
  rw [this]
  simp [f]; split_ifs <;> simp

-- LLM HELPER
theorem str2int_singleton (c : Char) : Str2Int (String.singleton c) = (if c = '1' then 1 else 0) := by
  dsimp [Str2Int]
  have : (String.singleton c).data = [c] := rfl
  rw [this]
  simp [List.foldl]

-- LLM HELPER
theorem rev_fold_bits_eq_str2int (s : String) :
  let l := s.data.reverse
  let g := fun (p : Nat × Nat) (ch : Char) => (p.1 + (if ch = '1' then p.2 else 0), 2 * p.2)
  (l.foldl g (0,1)).1 = Str2Int s := by
  -- Prove by induction on s.data
  let xs := s.data
  induction xs with
  | nil =>
    dsimp [rev_fold_bits_eq_str2int]; dsimp [Str2Int]
    -- empty string -> both sides 0
    simp
  | cons y ys ih =>
    dsimp [rev_fold_bits_eq_str2int]
    let l := (y :: ys).reverse
    -- (y :: ys).reverse = ys.reverse ++ [y]
    have : l = ys.reverse ++ [y] := by simp [l]
    rw [this]
    let g := fun (p : Nat × Nat) (ch : Char) => (p.1 + (if ch = '1' then p.2 else 0), 2 * p.2)
    -- foldl g (ys.reverse ++ [y]) (0,1) = fold over ys.reverse then over [y]
    have : (l.foldl g (0,1)).1 = ((ys.reverse).foldl g (0,1) |> fun p => (p.1 + (if y = '1' then p.2 else 0), 2 * p.2)).1 := by
      simp [List.foldl_append]
    rw [this]
    dsimp
    -- use induction hypothesis for ys
    have ih' := ih
    -- ih states: (ys.reverse.foldl g (0,1)).1 = Str2Int (String.mk (y :: ys)) without y? need to relate
    -- Build the string s = String.mk (y :: ys)
    let s' := String.mk (y :: ys)
    -- Apply ih to ys to get for s' without its head? We need relation between Str2Int s' and fold over ys.reverse
    -- Use direct computation:
    dsimp [Str2Int]
    -- compute Str2Int (String.mk (y :: ys)) = foldl f 0 (y :: ys) with f acc ch = 2*acc + (if ch='1' then 1 else 0)
    let f := fun (acc : Nat) (ch : Char) => 2 * acc + (if ch = '1' then 1 else 0)
    have : Str2Int (String.mk (y :: ys)) = List.foldl f 0 (y :: ys) := rfl
    rw [this]
    -- compute foldl f 0 (y :: ys) = f (List.foldl f 0 ys) y
    have : List.foldl f 0 (y :: ys) = f (List.foldl f 0 ys) y := by simp [List.foldl]
    rw [this]
    -- Now expand f
    simp [f]
    -- Now transform
-- </vc-code>

end BignumLean