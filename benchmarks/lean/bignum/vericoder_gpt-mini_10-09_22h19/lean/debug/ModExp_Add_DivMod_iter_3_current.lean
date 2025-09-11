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
    let rec aux : Nat → List Char
      | 0 => []
      | k => (aux (k / 2)) ++ [if k % 2 = 1 then '1' else '0']
    aux (n + 1)

/-- Build a String with exact `.data = l`. -/
def bits_to_string (l : List Char) : String := { data := l } -- LLM HELPER

theorem nat_to_bits_chars : ∀ n ch ∈ nat_to_bits n, ch = '0' ∨ ch = '1' := by
  intro n
  induction n using Nat.strong_induction_on with
  | ih n =>
    cases n with
    | zero =>
      simp [nat_to_bits]; intro ch h; simp at h; injection h with h'; subst h'; simp
    | succ n' =>
      dsimp [nat_to_bits]
      -- expose the auxiliary function used in nat_to_bits
      let rec aux : Nat → List Char
        | 0 => []
        | k => (aux (k / 2)) ++ [if k % 2 = 1 then '1' else '0']
      have aux_chars : ∀ k ch ∈ aux k, ch = '0' ∨ ch = '1' := by
        intro k
        induction k using Nat.strong_induction_on with
        | ihk k =>
          dsimp [aux]
          by_cases hk : k = 0
          · simp [hk]; intro ch hc; cases hc
          · -- aux k = aux (k/2) ++ [bit]
            intro ch hc
            have : aux k = (aux (k / 2)) ++ [if k % 2 = 1 then '1' else '0'] := rfl
            rw [this] at hc
            cases (List.mem_append.1 hc) with
            | inl hin =>
              exact (ihk (k / 2) (k / 2) (by apply hin))
            | inr heq =>
              injection heq with he; subst he
              simp
      apply aux_chars (n' + 1)

theorem nat_to_bits_fold (n : Nat) :
  (nat_to_bits n).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = n := by
  induction n using Nat.strong_induction_on with
  | ih n =>
    cases n with
    | zero => simp [nat_to_bits]
    | succ n' =>
      dsimp [nat_to_bits]
      let rec aux : Nat → List Char
        | 0 => []
        | k => (aux (k / 2)) ++ [if k % 2 = 1 then '1' else '0']
      have aux_fold : ∀ k, (aux k).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = k := by
        intro k
        induction k using Nat.strong_induction_on with
        | ihk k =>
          dsimp [aux]
          by_cases hk : k = 0
          · simp [hk]
          · -- aux k = aux (k/2) ++ [bit], use IH on k/2
            have : aux k = (aux (k / 2)) ++ [if k % 2 = 1 then '1' else '0'] := rfl
            rw [this]
            simp only [List.foldl_append]
            -- fold on single element: [b].foldl f acc = f acc b
            simp only [List.foldl]
            -- use IH on k/2
            have ih_val := ihk (k / 2) (k / 2) (by apply Nat.le_refl)
            -- compute bit value as Nat
            have bval : (if k % 2 = 1 then 1 else 0) = k % 2 := by
              cases Nat.mod_two_eq_zero_or_one k with
              | inl h => simp [h]; rfl
              | inr h => simp [h]; rfl
            -- now combine
            rw [ih_val, bval]
            -- now 2 * (k / 2) + k % 2 = k
            exact (Nat.div_mul_add_mod k 2).symm
      apply aux_fold (n + 1)

theorem bits_to_string_valid (l : List Char) (h : ∀ ch ∈ l, ch = '0' ∨ ch = '1') :
  ValidBitString (bits_to_string l) := by
  intro i c hg
  have : (bits_to_string l).get? i = l.get? i := rfl
  rw [this] at hg
  -- extract membership from List.get?_some_iff
  have mem := List.get?_some_iff.1 hg
  exact h _ mem

theorem bits_to_string_str2int (l : List Char) :
  Str2Int (bits_to_string l) = l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
  -- definition of Str2Int uses s.data.foldl ... and bits_to_string sets data := l
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