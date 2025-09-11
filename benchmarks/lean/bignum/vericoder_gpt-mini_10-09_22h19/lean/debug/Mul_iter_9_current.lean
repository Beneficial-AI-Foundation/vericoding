namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
/-- Build binary representation of a natural number as a list of chars '0'/'1'. -/
def nat_to_bin_list : Nat → List Char
| 0 => ['0']
| n+1 =>
  let m := n+1
  let q := m / 2
  let b := if m % 2 = 1 then '1' else '0'
  if q = 0 then [b] else nat_to_bin_list q ++ [b]
termination_by nat_to_bin_list _ => n
decreasing_by
  -- show q < n+1
  have : 1 < 2 := by norm_num
  exact Nat.div_lt_self (m := n+1) (b := 2) this

-- LLM HELPER
def nat_to_bin_string (n : Nat) : String := String.mk (nat_to_bin_list n)

-- LLM HELPER
/-- Helper: foldl property for our specific binary-accumulating function when appending one digit. -/
theorem foldl_append_one (l : List Char) (c : Char) :
    (l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) * 2 +
      (if c = '1' then 1 else 0) =
    (l ++ [c]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
  induction l with
  | nil => simp [List.foldl]
  | cons hd tl ih =>
    simp [List.foldl]
    have := ih
    simp [this]
    rfl

-- LLM HELPER
/-- Prove that nat_to_bin_list correctly encodes n as integer via Str2Int. -/
theorem nat_to_bin_list_spec (n : Nat) :
  Str2Int (String.mk (nat_to_bin_list n)) = n := by
  -- use strong induction on n
  apply Nat.strong_induction_on n
  intro m ih
  cases m with
  | zero =>
    simp [nat_to_bin_list, Str2Int, List.foldl]
  | succ k =>
    let m' := k+1
    let q := m' / 2
    let b := m' % 2
    let bchar := if b = 1 then '1' else '0'
    by_cases hq : q = 0
    · -- q = 0, so nat_to_bin_list m' = [bchar]
      have hdef : nat_to_bin_list m' = [bchar] := by simp [hq]
      calc
        Str2Int (String.mk (nat_to_bin_list m')) = Str2Int (String.mk [bchar]) := by simp [hdef]
        _ = (if bchar = '1' then 1 else 0) := by simp [Str2Int]; rfl
        _ = b := by
          dsimp [bchar]
          -- from m' = q * 2 + b and q = 0 we get m' = b, so b = m' and since m' > 0 this must be 1
          have eq := Nat.div_add_mod m' 2
          simp [hq] at eq
          -- eq : m' = b
          have : m' = b := eq
          subst this
          simp [b]; rfl
        _ = m' := by
          have eq := Nat.div_add_mod m' 2
          simp [hq] at eq
          simp [eq]
    · -- q ≠ 0
      have qlt : q < m' := Nat.div_lt_self (m := m') (b := 2) (by norm_num)
      have IHq := ih q qlt
      have hdef : nat_to_bin_list m' = nat_to_bin_list q ++ [bchar] := by simp [hq]
      calc
        Str2Int (String.mk (nat_to_bin_list m')) = Str2Int (String.mk (nat_to_bin_list q ++ [bchar])) := by simp [hdef]
        _ = (nat_to_bin_list q).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 * 2 + (if bchar = '1' then 1 else 0) := by
          simp [Str2Int]
          -- use foldl_append_one to relate foldl on append
          show (nat_to_bin_list q ++ [bchar]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
               (nat_to_bin_list q).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 * 2 + (if bchar = '1' then 1 else 0)
          apply Eq.symm
          apply foldl_append_one
        _ = q * 2 + b := by
          -- replace (nat_to_bin_list q).foldl ... with q using IHq
          simp [IHq]
          dsimp [bchar]
        _ = m' := by
          -- use div_add_mod: m' = q * 2 + b
          exact (Nat.div_add_mod m' 2)
-- </vc-helpers>

-- <vc-spec>
def Mul (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
def Mul (s1 s2 : String) : String :=
  nat_to_bin_string (Str2Int s1 * Str2Int s2)
-- </vc-code>

-- <vc-theorem>
theorem Mul_spec (s1 s2 : String) : Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2
-- </vc-theorem>
-- <vc-proof>
by
  simp [Mul, nat_to_bin_string]
  apply nat_to_bin_list_spec
-- </vc-proof>

end BignumLean