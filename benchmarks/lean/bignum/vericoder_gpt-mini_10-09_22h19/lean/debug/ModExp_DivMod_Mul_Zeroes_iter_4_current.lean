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
      rw [h1]
      simp
    | succ i' =>
      simp [List.get?] at h
      apply Or.inr
      exact ih tl i' c h

-- LLM HELPER
theorem Str2Int_nat_to_string (n : Nat) :
  Str2Int (nat_to_string n) = n := by
  apply Nat.strongInductionOn n; intro n ih
  dsimp [nat_to_string, nat_bits_ms]
  cases n with
  | zero =>
    -- nat_to_string 0 = String.mk ['0']
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
      have : m = n / 2 := rfl
      have m_zero : n / 2 = 0 := by rwa [this] at hm
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
    by_cases hm : m = 0
    · -- nat_bits_ms n = [b]
      have bits_eq : nat_bits_ms n = [b] := by dsimp [nat_bits_ms]; simp [hm]
      intro ch H
      simp [bits_eq] at H
      cases H
      · contradiction
      · simp [H]; dsimp [b]; cases (n % 2) with
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
  -- String.get? (String.mk ls) = ls.get? i, so from ls.get? i = some c we get c ∈ ls
  have : (String.mk ls).get? i = ls.get? i := by
    -- unfolding String.get? on a constructed string reduces to list.get?
    rfl
  have eq : ls.get? i = some c := by rwa [← this] at hc
  have mem := list_get?_mem ls i c eq
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