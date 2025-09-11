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
  rfl

-- LLM HELPER
theorem list_get?_mem {α} : ∀ (ls : List α) (i : Nat) (c : α), ls.get? i = some c → c ∈ ls := by
  intro ls
  induction ls with
  | nil =>
    intro i c h
    simp [List.get?] at h
    contradiction
  | cons hd tl ih =>
    intro i c h
    cases i with
    | zero =>
      simp [List.get?] at h
      injection h with h1
      subst h1
      left
      rfl
    | succ i' =>
      simp [List.get?] at h
      right
      exact ih i' c h

-- LLM HELPER
theorem String_mk_get?_eq (ls : List Char) (i : String.Pos) :
  (String.mk ls).get? i = ls.get? i.1 := by
  cases i with
  | mk k =>
    induction ls generalizing k with
    | nil =>
      simp [String.get?]; rfl
    | cons hd tl ih =>
      cases k with
      | zero =>
        simp [String.get?]; rfl
      | succ k' =>
        simp [String.get?]
        apply ih

-- LLM HELPER
theorem Str2Int_nat_to_string (n : Nat) :
  Str2Int (nat_to_string n) = n := by
  apply Nat.strongInductionOn n; intro n ih
  dsimp [nat_to_string, nat_bits_ms]
  cases n with
  | zero =>
    dsimp [nat_to_string, nat_bits_ms]
    calc
      Str2Int (nat_to_string 0) = Str2Int (String.mk ['0']) := rfl
      _ = ['0'].foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by apply Str2Int_String_mk
      _ = 0 := by simp [List.foldl]
  | succ k =>
    let n := k + 1
    let m := n / 2
    let b := if n % 2 = 1 then '1' else '0'
    by_cases hm : m = 0
    · -- case m = 0
      have bits_eq : nat_bits_ms n = [b] := by dsimp [nat_bits_ms]; simp [hm]
      dsimp [nat_to_string]
      calc
        Str2Int (nat_to_string n) = Str2Int (String.mk [b]) := by simp [bits_eq]
        _ = [b].foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by apply Str2Int_String_mk
        _ = (if b = '1' then 1 else 0) := by simp [List.foldl]
      -- show (if b='1' then 1 else 0) = n
      have m_zero : n / 2 = 0 := by rwa [←(rfl : m = n / 2)] at hm
      have : n < 2 := by
        have : n = 2 * (n / 2) + n % 2 := Nat.div_mod_eq n 2
        rw [m_zero] at this
        simp at this
        linarith
      have : n = 1 := by linarith
      dsimp [b]
      subst this
      simp
    · -- case m ≠ 0
      have bits_eq : nat_bits_ms n = nat_bits_ms m ++ [b] := by dsimp [nat_bits_ms]; simp [hm]
      dsimp [nat_to_string]
      calc
        Str2Int (nat_to_string n) = Str2Int (String.mk (nat_bits_ms m ++ [b])) := by simp [bits_eq]
        _ = (nat_bits_ms m ++ [b]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by apply Str2Int_String_mk
        _ = 2 * (nat_bits_ms m).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 + (if b = '1' then 1 else 0) := by
          simp [List.foldl_append]
        _ = 2 * (Str2Int (String.mk (nat_bits_ms m))) + (if b = '1' then 1 else 0) := by congr; apply Str2Int_String_mk
        _ = 2 * m + (if b = '1' then 1 else 0) := by
          have hm_lt : m < n := by
            have : m = n / 2 := rfl
            apply Nat.div_lt_self; linarith
          have ihm := ih m hm_lt
          exact congrArg (fun t => 2 * t + (if b = '1' then 1 else 0)) ihm
        _ = n := by
          have : m = n / 2 := rfl
          -- show (if b='1' then 1 else 0) = n % 2
          have bit_eq : (if b = '1' then 1 else 0) = n % 2 := by
            dsimp [b]
            have hmod : n % 2 < 2 := Nat.mod_lt n (by decide)
            cases (n % 2) with
            | zero => simp
            | succ k =>
              have : succ k = 1 := by
                have : succ k < 2 := by simpa using hmod
                cases k with
                | zero => rfl
                | succ _ => simp at this; contradiction
              simp [this]
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
    by_cases hm : m = 0
    · -- nat_bits_ms n = [b]
      have bits_eq : nat_bits_ms n = [b] := by dsimp [nat_bits_ms]; simp [hm]
      intro ch H
      simp [bits_eq] at H
      cases H with
      | head => contradiction
      | tail => simp [tail]; dsimp [b]; cases (n % 2) with
        | zero => simp
        | succ _ => simp
    · -- nat_bits_ms n = nat_bits_ms m ++ [b]
      have bits_eq : nat_bits_ms n = nat_bits_ms m ++ [b] := by dsimp [nat_bits_ms]; simp [hm]
      intro ch H
      rw [bits_eq] at H
      simp at H
      cases H with
      | inl Hmem =>
        have m_lt : m < n := by
          have : m = n / 2 := rfl
          apply Nat.div_lt_self; linarith
        exact ih m m_lt ch Hmem
      | inr Hlast =>
        simp [Hlast]; dsimp [b]; cases (n % 2) with
        | zero => simp
        | succ _ => simp

-- LLM HELPER
theorem ValidBitString_of_list {ls : List Char} (h : ∀ ch ∈ ls, ch = '0' ∨ ch = '1') :
  ValidBitString (String.mk ls) := by
  intro i c hc
  -- relate String.get? to underlying list index and use list_get?_mem
  have eq := String_mk_get?_eq ls i
  have : ls.get? i.1 = some c := by rwa [← eq] at hc
  have mem := list_get?_mem ls i.1 c this
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
  -- proof provided in vc-proof
-- </vc-theorem>
-- <vc-proof>
dsimp [ModExp, nat_to_string]
constructor
· -- valid bitstring property follows from nat_to_string construction
  apply ValidBitString_nat_to_string
· -- equality of Str2Int values follows from Str2Int_nat_to_string
  apply Str2Int_nat_to_string
-- </vc-proof>

end BignumLean