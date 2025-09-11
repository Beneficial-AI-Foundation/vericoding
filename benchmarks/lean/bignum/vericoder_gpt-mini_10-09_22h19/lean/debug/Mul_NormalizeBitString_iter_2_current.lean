namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def NormalizeBitString (s : String) : String :=
  sorry

axiom NormalizeBitString_spec (s : String) :
  ValidBitString (NormalizeBitString s) ∧
  (NormalizeBitString s).length > 0 ∧
  ((NormalizeBitString s).length > 1 → (NormalizeBitString s).get? 0 = some '1') ∧
  (ValidBitString s → Str2Int s = Str2Int (NormalizeBitString s))

-- <vc-helpers>
-- LLM HELPER
theorem foldl_bin_aux {α : Type} (f : Nat → Char → Nat) (b0 : Char) :
  -- specialized folding function used in Str2Int
  (fun (acc ch : Nat) => 2 * acc + (if (b0 : Char) = b0 then 0 else 0)) = fun _ _ => 0 := by
  -- dummy to satisfy formatting; not used

-- LLM HELPER
theorem foldl_bin (l : List Char) (acc : Nat) :
  l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) acc =
    acc * 2 ^ l.length + l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
  induction l with
  | nil =>
    simp [List.foldl, Nat.pow, Nat.mul_one, Nat.zero_add]
  | cons hd tl ih =>
    simp [List.foldl]
    have : (2 * (acc * 2 ^ tl.length + tl.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0)
             + (if hd = '1' then 1 else 0)) =
           acc * 2 ^ (tl.length + 1) + (2 * tl.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
             + (if hd = '1' then 1 else 0)) := by
      simp [Nat.mul_comm, Nat.pow_succ]
      rw [Nat.mul_add, Nat.mul_comm]
    rw [this]
    simp [List.foldl]
    congr
    exact ih

-- LLM HELPER
theorem Str2Int_append (s1 s2 : String) :
  Str2Int (s1 ++ s2) = (Str2Int s1) * 2 ^ (s2.length) + Str2Int s2 := by
  -- Str2Int uses data.foldl with the same folding function; use foldl_bin on the underlying lists
  have : (s1 ++ s2).data = s1.data ++ s2.data := by
    -- by definition of String.append
    rfl
  dsimp [Str2Int]
  conv => 
    lhs; rw [this]
  show (s1.data ++ s2.data).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
       (s1.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) * 2 ^ s2.data.length +
         s2.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
  have h := foldl_bin s2.data (s1.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0)
  simp at h
  exact h

-- LLM HELPER
def nat_to_bit_string : Nat → String
  | 0 => "0"
  | n+1 =>
    let m := (n+1) / 2
    let rest := nat_to_bit_string m
    let bit := if (n+1) % 2 = 1 then '1' else '0'
    rest ++ String.mk bit ""
  termination_by _ n => n
  decreasing_by
    exact Nat.div_lt_self (by decide)

-- LLM HELPER
theorem nat_to_bit_string_valid : ∀ n, ValidBitString (nat_to_bit_string n) := by
  intro n
  induction n with
  | zero => simp [nat_to_bit_string, ValidBitString]; intro i c; simp at *
    cases i <;> simp [String.get?]
    all_goals simp
  | succ n ih =>
    let k := n + 1
    have : nat_to_bit_string k =
-- </vc-helpers>

-- <vc-spec>
def Mul (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
theorem foldl_bin_aux {α : Type} (f : Nat → Char → Nat) (b0 : Char) :
  -- specialized folding function used in Str2Int
  (fun (acc ch : Nat) => 2 * acc + (if (b0 : Char) = b0 then 0 else 0)) = fun _ _ => 0 := by
  -- dummy to satisfy formatting; not used

-- LLM HELPER
theorem foldl_bin (l : List Char) (acc : Nat) :
  l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) acc =
    acc * 2 ^ l.length + l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
  induction l with
  | nil =>
    simp [List.foldl, Nat.pow, Nat.mul_one, Nat.zero_add]
  | cons hd tl ih =>
    simp [List.foldl]
    have : (2 * (acc * 2 ^ tl.length + tl.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0)
             + (if hd = '1' then 1 else 0)) =
           acc * 2 ^ (tl.length + 1) + (2 * tl.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
             + (if hd = '1' then 1 else 0)) := by
      simp [Nat.mul_comm, Nat.pow_succ]
      rw [Nat.mul_add, Nat.mul_comm]
    rw [this]
    simp [List.foldl]
    congr
    exact ih

-- LLM HELPER
theorem Str2Int_append (s1 s2 : String) :
  Str2Int (s1 ++ s2) = (Str2Int s1) * 2 ^ (s2.length) + Str2Int s2 := by
  -- Str2Int uses data.foldl with the same folding function; use foldl_bin on the underlying lists
  have : (s1 ++ s2).data = s1.data ++ s2.data := by
    -- by definition of String.append
    rfl
  dsimp [Str2Int]
  conv => 
    lhs; rw [this]
  show (s1.data ++ s2.data).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
       (s1.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) * 2 ^ s2.data.length +
         s2.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
  have h := foldl_bin s2.data (s1.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0)
  simp at h
  exact h

-- LLM HELPER
def nat_to_bit_string : Nat → String
  | 0 => "0"
  | n+1 =>
    let m := (n+1) / 2
    let rest := nat_to_bit_string m
    let bit := if (n+1) % 2 = 1 then '1' else '0'
    rest ++ String.mk bit ""
  termination_by _ n => n
  decreasing_by
    exact Nat.div_lt_self (by decide)

-- LLM HELPER
theorem nat_to_bit_string_valid : ∀ n, ValidBitString (nat_to_bit_string n) := by
  intro n
  induction n with
  | zero => simp [nat_to_bit_string, ValidBitString]; intro i c; simp at *
    cases i <;> simp [String.get?]
    all_goals simp
  | succ n ih =>
    let k := n + 1
    have : nat_to_bit_string k =
-- </vc-code>

end BignumLean