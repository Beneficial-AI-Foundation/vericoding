namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def Add (s1 s2 : String) : String :=
  sorry

axiom Add_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Add s1 s2) ∧ Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2

def DivMod (dividend divisor : String) : (String × String) :=
  sorry

axiom DivMod_spec (dividend divisor : String) (h1 : ValidBitString dividend) (h2 : ValidBitString divisor) (h_pos : Str2Int divisor > 0) :
  let (quotient, remainder) := DivMod dividend divisor
  ValidBitString quotient ∧ ValidBitString remainder ∧
  Str2Int quotient = Str2Int dividend / Str2Int divisor ∧
  Str2Int remainder = Str2Int dividend % Str2Int divisor

-- <vc-helpers>
-- LLM HELPER
def nat_to_bits : Nat → List Char
  | 0 => ['0']
  | n+1 =>
    let m := n+1
    let q := m / 2
    let b := if m % 2 = 1 then '1' else '0'
    (nat_to_bits q) ++ [b]
  termination_by _ => n+1
  decreasing_by
    -- show q < n+1 where q = (n+1) / 2
    apply Nat.div_lt_self (Nat.zero_lt_succ n)

/-- Build a String with exact `.data = l`. -/ -- LLM HELPER
def bits_to_string (l : List Char) : String := { data := l }

theorem nat_to_bits_chars : ∀ n ch, ch ∈ nat_to_bits n → ch = '0' ∨ ch = '1' := by
  apply Nat.strong_induction_on
  intro m ih
  intro ch h
  cases m with
  | zero =>
    -- nat_to_bits 0 = ['0']
    simp [nat_to_bits] at h
    cases h with
    | head => simp [head]; exact Or.inl rfl
    | tail => contradiction
  | succ k =>
    let m := k+1
    dsimp [nat_to_bits] at h
    let q := m / 2
    let b := if m % 2 = 1 then '1' else '0'
    have hq : q < m := Nat.div_lt_self (Nat.zero_lt_succ k)
    simp only [List.mem_append] at h
    cases h with
    | inl hin => exact ih q hq ch hin
    | inr hin =>
      -- ch ∈ [b]
      simp at hin
      have : ch = b := hin
      rw [this]
      by_cases hb : m % 2 = 1
      · simp [hb]; exact Or.inr rfl
      · simp [hb]; exact Or.inl rfl

theorem nat_to_bits_fold (n : Nat) :
  (nat_to_bits n).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = n := by
  apply Nat.strong_induction_on
  intro m ih
  cases m with
  | zero =>
    simp [nat_to_bits]
    simp
  | succ k =>
    let m := k+1
    dsimp [nat_to_bits]
    let q := m / 2
    let b := if m % 2 = 1 then '1' else '0'
    have hq : q < m := Nat.div_lt_self (Nat.zero_lt_succ k)
    -- fold on (nat_to_bits q ++ [b])
    have f_append := List.foldl_append (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 (nat_to_bits q) [b]
    rw [f_append]
    -- fold on prefix equals q by IH
    have ihq := ih q hq
    rw [ihq]
    -- value of b equals m % 2
    by_cases hb : m % 2 = 1
    · simp [hb]
    · simp [hb]
    -- combine: 2 * q + m % 2 = m
    exact (Nat.div_mul_add_mod m 2).symm

theorem bits_to_string_valid (l : List Char) (h : ∀ ch ∈ l, ch = '0' ∨ ch = '1') :
  ValidBitString (bits_to_string l) := by
  intro i c hg
  -- use the fact that bits_to_string was built with `.data = l`, so characters returned come from l
  -- reduce to the corresponding list-get and then use the hypothesis h
  have : (bits_to_string l).data = l := rfl
  -- rewrite the underlying data and use List.get?_mem to obtain membership
  -- Note: `String.get?` and `List.get?` are definitionally related when the string is built via `{ data := l }`
  have eq := congrArg (fun s => s.get? i) this
  dsimp at eq
  -- now rewrite hg to a statement about l.get? and obtain membership
  rw [← eq] at hg
  have mem := List.get?_mem.1 hg
  exact h _ mem

theorem bits_to_string_str2int (l : List Char) :
  Str2Int (bits_to_string l) = l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
  -- Str2Int only inspects `.data` so this is true by definition
  rfl
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
def ModExp (sx sy sz : String) : String :=
  let base := Str2Int sx % Str2Int sz
  let exp := Str2Int sy
  let res := Exp_int base exp % Str2Int sz
  bits_to_string (nat_to_bits res)
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (h1 : ValidBitString sx) (h2 : ValidBitString sy) (h3 : ValidBitString sz) (h_pos : Str2Int sz > 0) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx % Str2Int sz) (Str2Int sy) % Str2Int sz
-- </vc-theorem>
-- <vc-proof>
proof :=
  fun sx sy sz h1 h2 h3 h_pos => by
    dsimp [ModExp]
    let val := Exp_int (Str2Int sx % Str2Int sz) (Str2Int sy) % Str2Int sz
    -- validity: nat_to_bits produces only '0'/'
-- </vc-proof>

end BignumLean