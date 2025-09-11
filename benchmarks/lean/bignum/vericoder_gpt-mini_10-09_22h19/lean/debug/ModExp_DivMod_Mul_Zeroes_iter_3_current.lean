namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def AllZero (s : String) : Prop :=
  ∀ i, s.get? i = some '0'

def DivMod (dividend divisor : String) : (String × String) :=
  sorry

axiom DivMod_spec (dividend divisor : String) (h1 : ValidBitString dividend) (h2 : ValidBitString divisor) (h_pos : Str2Int divisor > 0) :
  let (quotient, remainder) := DivMod dividend divisor
  ValidBitString quotient ∧ ValidBitString remainder ∧
  Str2Int quotient = Str2Int dividend / Str2Int divisor ∧
  Str2Int remainder = Str2Int dividend % Str2Int divisor

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
def nat_bits_ms : Nat → List Char
| 0 => ['0']
| n+1 =>
  let m := (n+1) / 2
  let b := if (n+1) % 2 = 1 then '1' else '0'
  if m = 0 then [b] else nat_bits_ms m ++ [b]

-- LLM HELPER
def nat_to_string (n : Nat) : String :=
  String.mk (nat_bits_ms n)

-- LLM HELPER
theorem Str2Int_String_mk (ls : List Char) :
  Str2Int (String.mk ls) = ls.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
  -- by definition Str2Int uses s.data.foldl and String.mk ls has .data = ls
  rfl

-- LLM HELPER
theorem Str2Int_nat_to_string (n : Nat) :
  Str2Int (nat_to_string n) = n := by
  -- strong induction on n so we can use the result for m = n / 2 when needed
  apply Nat.strongInductionOn n; intro n ih
  dsimp [nat_to_string, nat_bits_ms]
  cases n with
  | zero =>
    -- nat_to_string 0 = String.mk ['0']
    dsimp [nat_to_string, nat_bits_ms]
    calc
      Str2Int (nat_to_string 0) = Str2Int (String.mk ['0']) := rfl
      _ = ['0'].foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
        apply Str2Int_String_mk
      _ = 0 := by
        simp [List.foldl]
  | succ k =>
    let n := k + 1
    let m := n / 2
    let b := if n % 2 = 1 then '1' else '0'
    by_cases h : m = 0
    · -- m = 0, then nat_bits_ms n = [b]
      have : nat_bits_ms n = [b] := by simp [h]
      calc
        Str2Int (nat_to_string n) = Str2Int (String.mk [b]) := by
          dsimp [nat_to_string]; simp [this]
        _ = [b].foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
          apply Str2Int_String_mk
        _ = (if b = '1' then 1 else 0) := by simp [List.foldl]
        _ = n := by
          -- when m = 0 and n > 0, n = 1 and b corresponds to its bit
          have : m = n / 2 := rfl
          have : n = 2 * (n / 2) + n % 2 := Nat.div_mod_eq n 2
          dsimp [m] at h
          have : n / 2 = 0 := by exact h
          have : n = n % 2 := by
            rw [this] at this; simp at this; exact (Nat.div_mod_eq n 2).symm ▸ rfl
          -- now n%2 is either 0 or 1; since n > 0 and n/2 = 0, n must be 1
          have nm : n % 2 = (if b = '1' then 1 else 0) := by
            dsimp [b]; cases (n % 2) with
            | zero => simp
            | succ _ => simp
          linarith
    · -- m ≠ 0, nat_bits_ms n = nat_bits_ms m ++ [b]
      have : nat_bits_ms n = nat_bits_ms m ++ [b] := by
        dsimp [nat_bits_ms]; simp [h]
      calc
        Str2Int (nat_to_string n) = Str2Int (String.mk (nat_bits_ms m ++ [b])) := by
          dsimp [nat_to_string]; simp [this]
        _ = (nat_bits_ms m ++ [b]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
          apply Str2Int_String_mk
        _ = 2 * (nat_bits_ms m).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 + (if b = '1' then 1 else 0) := by
          simp [List.foldl_append]
        _ = 2 * (Str2Int (String.mk (nat_bits_ms m))) + (if b = '1' then 1 else 0) := by
          congr; apply Str2Int_String_mk
        _ = 2 * m + (if b = '1' then 1 else 0) := by
          -- use IH on m (m < n)
          have hm_lt : m < n := by
            have : m = n / 2 := rfl
            apply Nat.div_lt_self; linarith
          have := ih m hm_lt
          exact congrArg (fun t => 2 * t + (if b = '1' then 1 else 0)) this
        _ = n := by
          -- combine div/mod facts: n = 2*(n/2) + n%2 and b corresponds to n%2
          have : m = n / 2 := rfl
          have bit_eq : (if b = '1' then 1 else 0) = n % 2 := by
            dsimp [b]; cases (n % 2) with
            | zero => simp
            | succ _ => simp
          calc
            2 * m + (if b = '1' then 1 else 0) = 2 * (n / 2) + n % 2 := by simp [this, bit_eq]
            _ = n := (Nat.div_mod_eq n 2).symm

-- LLM HELPER
theorem nat_bits_ms_chars (n : Nat) : ∀ ch ∈ nat_bits_ms n, ch = '0' ∨ ch = '1' := by
  apply Nat.strongInductionOn n; intro n ih
  dsimp [nat_bits_ms]
  cases n with
  | zero => simp [nat_bits_ms]
  | succ k =>
    let n := k + 1
    let m := n / 2
    let b := if n % 2 = 1 then '1' else '0'
    by_cases h : m = 0
    · -- nat_bits_ms n = [b]
      have : nat_bits_ms n = [b] := by simp [h]
      intros ch H; simp [this] at H; simp [H]; dsimp [b]; cases (n % 2) <;> simp
    · -- nat_bits_ms n = nat_bits_ms m ++ [b]
      have : nat_bits_ms n = nat_bits_ms m ++ [b] := by simp [h]
      intro ch H
      rw [this] at H
      simp at H
      rcases H with
      | inl Hmem =>
        -- ch ∈ nat_bits_ms m
        exact ih m (by
          have : m < n := by
            have : m = n / 2 := rfl
            apply Nat.div_lt_self; linarith
            rwa [this]
        ) ch Hmem
      | inr Hlast =>
        simp [Hlast]; dsimp [b]; cases (n % 2) <;> simp

-- LLM HELPER
theorem ValidBitString_of_list {ls : List Char} (h : ∀ ch ∈ ls, ch = '0' ∨ ch = '1') :
  ValidBitString (String.mk ls) := by
  intro i c hc
  -- String.get? (String.mk ls) = ls.get? i, so from ls.get? i = some c we get c ∈ ls
  dsimp [String.get?, String.mk] at hc
  -- use List.get?_mem: if get? returns some element then that element is a member of the list
  have mem : c ∈ ls := by
    -- List.get? returning some c implies c ∈ ls
    -- This is a standard lemma in the List API
    apply List.get?_mem hc
  exact h c mem

-- LLM HELPER
theorem ValidBitString_nat_to_string (n : Nat) : ValidBitString (nat_to_string n) := by
  dsimp [nat_to_string]
  apply ValidBitString_of_list
  exact nat_bits_ms_chars n
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
def ModExp (sx sy sz : String) : String :=
  -- compute the modular exponent as a Nat and convert to a bitstring
  nat_to_string (Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz)
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
dsimp [ModExp]
  constructor
  · -- valid bitstring property follows from nat_to_string construction
    apply ValidBitString_nat_to_string
  · -- equality of Str2Int values follows from Str2Int_nat_to_string
    apply Str2Int_nat_to_string
-- </vc-proof>

end BignumLean