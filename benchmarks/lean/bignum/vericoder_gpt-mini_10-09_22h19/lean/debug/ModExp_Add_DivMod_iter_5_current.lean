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
  | k+1 =>
    let n := k+1
    let q := n / 2
    let b := if n % 2 = 1 then '1' else '0'
    (nat_to_bits q) ++ [b]
  termination_by _ k => k
  decreasing_by
    -- show (k+1)/2 < k+1
    apply Nat.div_lt_self (Nat.zero_lt_succ k)

/-- Build a String with exact `.data = l`. -/ -- LLM HELPER
def bits_to_string (l : List Char) : String := { data := l }

theorem nat_to_bits_chars : ∀ n ch, ch ∈ nat_to_bits n → ch = '0' ∨ ch = '1' := by
  intro n
  apply Nat.strong_induction_on n
  intro n ih ch h
  cases n with
  | zero =>
    -- nat_to_bits 0 = ['0']
    simp [nat_to_bits] at h
    simp at h
    cases h with
    | inl heq => subst heq; simp; exact Or.inl rfl
    | inr _ => contradiction
  | succ k =>
    let n := k+1
    dsimp [nat_to_bits] at h
    let q := n / 2
    let b := if n % 2 = 1 then '1' else '0'
    have hq : q < n := Nat.div_lt_self (Nat.zero_lt_succ k)
    simp only [List.mem_append] at h
    cases h with
    | inl hin => exact ih q hq ch hin
    | inr hin =>
      -- ch ∈ [b], so ch = b and b is either '0' or '1'
      simp at hin
      have : ch = b := hin
      rw [this]
      by_cases hb : n % 2 = 1
      · simp [hb]; exact Or.inr rfl
      · simp [hb]; exact Or.inl rfl

theorem nat_to_bits_fold (n : Nat) :
  (nat_to_bits n).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = n := by
  apply Nat.strong_induction_on n
  intro n ih
  cases n with
  | zero =>
    simp [nat_to_bits]
    -- ['0'] folds to 0
    simp
  | succ k =>
    let n := k+1
    dsimp [nat_to_bits]
    let q := n / 2
    let b := if n % 2 = 1 then '1' else '0'
    have hq : q < n := Nat.div_lt_self (Nat.zero_lt_succ k)
    -- fold on (nat_to_bits q ++ [b])
    have f_append := List.foldl_append (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 (nat_to_bits q) [b]
    dsimp [List.foldl] at f_append
    rw [f_append]
    -- fold on prefix equals q by IH
    have ihq := ih q hq
    rw [ihq]
    -- value of b equals n % 2
    have bval : (if n % 2 = 1 then 1 else 0) = n % 2 := by
      cases Nat.mod_two_eq_zero_or_one n with
      | inl h => simp [h]
      | inr h => simp [h]
    rw [bval]
    -- combine: 2 * q + n % 2 = n
    exact (Nat.div_mul_add_mod n 2).symm
    -- note: List.foldl_append and other lemmas give required rewrites

theorem bits_to_string_valid (l : List Char) (h : ∀ ch ∈ l, ch = '0' ∨ ch = '1') :
  ValidBitString (bits_to_string l) := by
  intro i c hg
  have : (bits_to_string l).get? i = l.get? i := rfl
  rw [this] at hg
  -- from l.get? i = some c we get that c is a member of l
  have mem := (List.get?_some_iff.1 hg)
  -- List.get?_some_iff yields existence of index; extract element equality to show membership
  cases mem with
  | intro _ hlen =>
    -- hlen gives that l.get?_some... but we can reason: if l.get? j = some c then c ∈ l
    -- There's a standard lemma: List.get?_some_iff provides j and then List.get?_eq... we can show c ∈ l
    -- Use List.get?_some_iff to produce an index and then List.get?_mem to conclude membership
    -- The following composes these standard facts:
    have : c ∈ l := by
      -- construct: there exists index j with l.get? j = some c and j < l.length
      -- mem_of_get?_eq_some is available via List.get?_some_iff -> but we can directly use List.get?_mem
      -- Lean's library provides List.get?_mem, but if not, we can observe that get?_eq_some implies membership:
      -- convert the witness from List.get?_some_iff
      rcases List.get?_some_iff.1 hg with ⟨j, hj⟩
      -- hj : l.get? j = some c
      exact List.mem_of_get?_eq_some hj
    exact h _ this

theorem bits_to_string_str2int (l : List Char) :
  Str2Int (bits_to_string l) = l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
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
    -- validity: nat_to_bits produces only '0'/'1', so bits_to_string is valid
    have chars := nat_to_bits_chars val
    have v := bits_to_string_valid (nat_to_bits val) chars
    -- numeric equality: Str2Int (bits_to_string l) = l.foldl ... by def
    have eq1 := bits_to_string_str2int (nat_to_bits val)
    -- and nat_to_bits_fold gives that foldl equals val
    have eq2 := nat_to_bits_fold val
    refine And.intro v ?_
    calc
      Str2Int (bits_to_string (nat_to_bits val)) = (nat_to_bits val).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := eq1
      _ = val := eq2
-- </vc-proof>

end BignumLean