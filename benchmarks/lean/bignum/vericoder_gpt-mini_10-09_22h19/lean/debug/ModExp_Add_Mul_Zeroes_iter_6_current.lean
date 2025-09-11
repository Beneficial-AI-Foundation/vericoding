namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def AllZero (s : String) : Prop :=
  ∀ i, s.get? i = some '0'

def Add (s1 s2 : String) : String :=
  sorry

axiom Add_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Add s1 s2) ∧ Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2

def Mul (s1 s2 : String) : String :=
  sorry

axiom Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2

def Zeros (n : Nat) : String :=
  sorry

axiom Zeros_spec (n : Nat) :
  let s := Zeros n
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ AllZero s

-- <vc-helpers>
-- LLM HELPER
def nat_bits_aux : Nat → List Char := fun n =>
  match n with
  | 0 => []
  | n+1 =>
    let b := if (n+1) % 2 = 1 then '1' else '0'
    nat_bits_aux ((n+1) / 2) ++ [b]

termination_by nat_bits_aux n => n
decreasing_by
  intro n
  cases n with
  | zero => simp
  | succ _ =>
    -- ((n'.succ) / 2) < n'.succ
    exact Nat.div_lt_self (by norm_num : (0 : Nat) < 2)

-- LLM HELPER
def nat_bits (n : Nat) : List Char :=
  if n = 0 then ['0'] else nat_bits_aux n

-- LLM HELPER
def nat_to_string (n : Nat) : String :=
  String.mk (nat_bits n)

-- LLM HELPER
theorem nat_bits_aux_spec (n : Nat) :
  (nat_bits_aux n).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = n := by
  induction n using Nat.strong_induction_on with
  | ih k =>
    cases k with
    | zero => simp [nat_bits_aux]
    | succ k' =>
      let m := (succ k') / 2
      have hm : m < succ k' := by
        exact Nat.div_lt_self (by norm_num : (0 : Nat) < 2)
      dsimp [nat_bits_aux]
      let digit := if (succ k') % 2 = 1 then '1' else '0'
      calc
        (nat_bits_aux (succ k')).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
          = (nat_bits_aux m ++ [digit]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := rfl
        _ = 2 * ((nat_bits_aux m).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) + (if digit = '1' then 1 else 0) := by
          simp [List.foldl_append]
        _ = 2 * m + (if (succ k') % 2 = 1 then 1 else 0) := by
          congr
          exact ih m hm
        _ = succ k' := by
          have : succ k' = 2 * ((succ k') / 2) + (succ k') % 2 := Nat.div_add_mod (succ k') 2
          dsimp [digit] at this ⊢
          rw [this]

-- LLM HELPER
theorem nat_to_string_Str2Int (n : Nat) :
  Str2Int (nat_to_string n) = n := by
  dsimp [nat_to_string, nat_bits]
  by_cases hn : n = 0
  · simp [hn, Str2Int]
  · -- n > 0
    dsimp [nat_bits]; simp [hn]
    dsimp [Str2Int]
    -- now apply nat_bits_aux_spec
    exact nat_bits_aux_spec n

-- LLM HELPER
theorem ValidBitString_nat_to_string (n : Nat) : ValidBitString (nat_to_string n) := by
  intro i c h
  dsimp [nat_to_string, nat_bits] at h
  by_cases hn : n = 0
  · -- only '0'
    simp [hn] at h
    cases h with
    | intro _ heq =>
      subst heq
      left; rfl
  · -- n > 0, use nat_bits_aux which only inserts '0'/'1'
    dsimp [nat_bits] at h
    -- now nat_bits n = nat_bits_aux n
    have hb : nat_bits n = nat_bits_aux n := by simp [hn]
    subst hb
    -- prove all chars are '0' or '1' by strong induction on n
    induction n using Nat.strong_induction_on with
    | ih k =>
      cases k with
      | zero => simp at hn; contradiction
      | succ k' =>
        let m := (succ k') / 2
        have hm : m < succ k' := by
          exact Nat.div_lt_self (by norm_num : (0 : Nat) < 2)
        dsimp [nat_bits_aux] at h
        let digit := if (succ k') % 2 = 1 then '1' else '0'
        simp [List.mem_append] at h
        cases h
        · -- element comes from prefix nat_bits_aux m
          apply ih m hm h
        · -- element is the last digit
          cases h with
          | intro _ heq =>
            subst heq
            dsimp [digit]
            left; rfl
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
def ModExp (sx sy sz : String) : String :=
  -- compute numeric result and convert to bitstring
  let r := Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz
  nat_to_string r
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
have r := Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz
dsimp [ModExp]
constructor
· apply ValidBitString_nat_to_string
· exact nat_to_string_Str2Int r
-- </vc-proof>

end BignumLean