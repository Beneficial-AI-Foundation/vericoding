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

def Mul (s1 s2 : String) : String :=
  sorry

axiom Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2

-- <vc-helpers>
-- LLM HELPER
def bits_rev : Nat → List Char
| 0     => []
| n + 1 =>
  let m := n + 1
  let c := if m % 2 = 1 then '1' else '0'
  c :: bits_rev (m / 2)

-- LLM HELPER
def list_to_nat (l : List Char) : Nat :=
  l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- LLM HELPER
def string_of_chars (l : List Char) : String :=
  l.foldl (fun s c => String.push s c) ""

-- LLM HELPER
def nat_to_str : Nat → String
| 0     => "0"
| n + 1 =>
  let l := (bits_rev (n + 1)).reverse
  string_of_chars l

-- LLM HELPER
theorem bits_rev_only_bits : ∀ n c, c ∈ bits_rev n → (c = '0' ∨ c = '1') := by
  intro n
  induction n with
  | zero =>
    intros c h
    simp [bits_rev] at h
    contradiction
  | succ k ih =>
    intros c h
    simp [bits_rev] at h
    cases h
    · -- head case
      simp_all
      left; rfl
    · -- tail case
      apply ih; assumption

-- LLM HELPER
theorem list_to_nat_reverse_bits_rev (n : Nat) :
  list_to_nat ((bits_rev n).reverse) = n := by
  induction n with
  | zero => simp [bits_rev, list_to_nat]
  | succ k =>
    let m := k + 1
    have h_bits : bits_rev m = (if m % 2 = 1 then '1' else '0') :: bits_rev (m / 2) := rfl
    have rev_eq : (bits_rev m).reverse = (bits_rev (m / 2)).reverse ++ [if m % 2 = 1 then '1' else '0'] := by
      simp [h_bits]; exact (List.reverse_cons _ _).symm
    rw [rev_eq, list_to_nat, List.foldl_append]
    -- fold over append: foldl f acc (l ++ [b]) = foldl f acc l |> f b
    simp
    have ih := list_to_nat_reverse_bits_rev (m / 2)
    rw [ih]
    -- now 2 * (m / 2) + bit = m
    have div_add_mod := Nat.div_add_mod m 2
    -- bit equals m % 2
    have bit_eq : (if m % 2 = 1 then 1 else 0) = m % 2 := by
      have hlt : m % 2 < 2 := Nat.mod_lt m (by decide)
      cases (m % 2) with
      | zero => simp
      | succ r =>
        -- the only succ less than 2 is 1
        have : m % 2 = 1 := by
          have : m % 2 ≤ 1 := Nat.le_of_lt_succ (by exact hlt)
          cases (m % 2) <;> simp at this
        simp [this]
    rw [bit_eq] at div_add_mod
    exact div_add_mod

-- LLM HELPER
theorem string_of_chars_data {l : List Char} :
  (string_of_chars l).data = l := by
  induction l with
  | nil =>
    simp [string_of_chars]; rfl
  | cons hd tl ih =>
    simp [string_of_chars, List.foldl]
    induction tl with
    | nil =>
      simp
    | cons h t ih2 =>
      simp [List.foldl] at *
      -- foldl (push) (push "" hd) (h :: t)
-- </vc-helpers>

-- <vc-spec>
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
def bits_rev : Nat → List Char
| 0     => []
| n + 1 =>
  let m := n + 1
  let c := if m % 2 = 1 then '1' else '0'
  c :: bits_rev (m / 2)

-- LLM HELPER
def list_to_nat (l : List Char) : Nat :=
  l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- LLM HELPER
def string_of_chars (l : List Char) : String :=
  l.foldl (fun s c => String.push s c) ""

-- LLM HELPER
def nat_to_str : Nat → String
| 0     => "0"
| n + 1 =>
  let l := (bits_rev (n + 1)).reverse
  string_of_chars l

-- LLM HELPER
theorem bits_rev_only_bits : ∀ n c, c ∈ bits_rev n → (c = '0' ∨ c = '1') := by
  intro n
  induction n with
  | zero =>
    intros c h
    simp [bits_rev] at h
    contradiction
  | succ k ih =>
    intros c h
    simp [bits_rev] at h
    cases h
    · -- head case
      simp_all
      left; rfl
    · -- tail case
      apply ih; assumption

-- LLM HELPER
theorem list_to_nat_reverse_bits_rev (n : Nat) :
  list_to_nat ((bits_rev n).reverse) = n := by
  induction n with
  | zero => simp [bits_rev, list_to_nat]
  | succ k =>
    let m := k + 1
    have h_bits : bits_rev m = (if m % 2 = 1 then '1' else '0') :: bits_rev (m / 2) := rfl
    have rev_eq : (bits_rev m).reverse = (bits_rev (m / 2)).reverse ++ [if m % 2 = 1 then '1' else '0'] := by
      simp [h_bits]; exact (List.reverse_cons _ _).symm
    rw [rev_eq, list_to_nat, List.foldl_append]
    -- fold over append: foldl f acc (l ++ [b]) = foldl f acc l |> f b
    simp
    have ih := list_to_nat_reverse_bits_rev (m / 2)
    rw [ih]
    -- now 2 * (m / 2) + bit = m
    have div_add_mod := Nat.div_add_mod m 2
    -- bit equals m % 2
    have bit_eq : (if m % 2 = 1 then 1 else 0) = m % 2 := by
      have hlt : m % 2 < 2 := Nat.mod_lt m (by decide)
      cases (m % 2) with
      | zero => simp
      | succ r =>
        -- the only succ less than 2 is 1
        have : m % 2 = 1 := by
          have : m % 2 ≤ 1 := Nat.le_of_lt_succ (by exact hlt)
          cases (m % 2) <;> simp at this
        simp [this]
    rw [bit_eq] at div_add_mod
    exact div_add_mod

-- LLM HELPER
theorem string_of_chars_data {l : List Char} :
  (string_of_chars l).data = l := by
  induction l with
  | nil =>
    simp [string_of_chars]; rfl
  | cons hd tl ih =>
    simp [string_of_chars, List.foldl]
    induction tl with
    | nil =>
      simp
    | cons h t ih2 =>
      simp [List.foldl] at *
      -- foldl (push) (push "" hd) (h :: t)
-- </vc-code>

end BignumLean