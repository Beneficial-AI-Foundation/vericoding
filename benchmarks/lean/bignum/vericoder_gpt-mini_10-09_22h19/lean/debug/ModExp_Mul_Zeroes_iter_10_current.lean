namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def AllZero (s : String) : Prop :=
  ∀ i, s.get? i = some '0'

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
def nat_to_bits : Nat -> List Char
  | 0 => ['0']
  | k+1 =>
    let m := (k+1) / 2
    let b := if (k+1) % 2 = 1 then '1' else '0'
    nat_to_bits m ++ [b]
decreasing_by
  dsimp [Nat.div]
  apply Nat.div_lt_self
  · exact Nat.succ_pos k
  · decide

-- LLM HELPER
def Nat_to_BinString (n : Nat) : String :=
  String.mk (nat_to_bits n)

-- LLM HELPER
theorem get?_mem {α : Type _} (l : List α) (i : Nat) (x : α) (h : l.get? i = some x) : x ∈ l := by
  induction l with
  | nil =>
    simp [List.get?] at h
    contradiction
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp [List.get?] at h
      injection h with hx
      subst hx
      simp
    | succ i' =>
      simp [List.get?] at h
      apply Or.inr
      apply ih
      exact h

-- LLM HELPER
theorem nat_to_bits_members (n : Nat) :
  ∀ {c}, c ∈ nat_to_bits n → (c = '0' ∨ c = '1') := by
  apply Nat.strong_induction_on n
  intro m ih c h
  cases m with
  | zero =>
    simp [nat_to_bits] at h
    rcases h with ⟨rfl | contra⟩
    · simp_all
    · contradiction
  | succ k =>
    let m' := m
    let q := m' / 2
    let b := if m' % 2 = 1 then '1' else '0'
    have H : nat_to_bits m' = nat_to_bits q ++ [b] := rfl
    simp [H] at h
    cases List.mem_append.1 h with
    | inl hin =>
      have q_lt : q < m' := by
        apply Nat.div_lt_self
        · exact Nat.succ_pos k
        · decide
      exact ih q q_lt c hin
    | inr hin =>
      simp at hin
      injection hin with hc
      subst hc
      by_cases hmod : m' % 2 = 1
      · simp [b, hmod]; right; rfl
      · simp [b, hmod]; left; rfl

-- LLM HELPER
theorem nat_to_bits_valid_string (n : Nat) :
  ValidBitString (Nat_to_BinString n) := by
  intro i c h
  -- unfold String.mk.get? to the underlying list.get? using the positional index
  simp [Nat_to_BinString, String.get?] at h
  -- now h is (nat_to_bits n).get? (i.toNat) = some c
  have mem := get?_mem (nat_to_bits n) (i.toNat) c h
  exact nat_to_bits_members n mem

-- LLM HELPER
theorem Str2Int_nat_to_bits (n : Nat) :
  Str2Int (Nat_to_BinString n) = n := by
  apply Nat.strong_induction_on n
  intro m ih
  cases m with
  | zero =>
    simp [Nat_to_BinString, nat_to_bits, Str2Int]
    rfl
  | succ k =>
    let m' := m
    let q := m' / 2
    let b := if m' % 2 = 1 then '1' else '0'
    have H : nat_to_bits m' = nat_to_bits q ++ [b] := rfl
    simp [Nat_to_BinString, Str2Int, H]
    -- foldl append lemma
    have foldl_append := List.foldl_append (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 (nat_to_bits q) [b]
    rw [foldl_append]
    -- use IH for q (q < m')
    have q_lt : q < m' := by
      apply Nat.div_lt_self
      · exact Nat.succ_pos k
      · decide
    have ih_q := ih q q_lt
    have : (nat_to_bits q).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = q := by
      simp [Str2Int, Nat_to_BinString] at ih_q
      exact ih_q
    rw [this]
    -- reduce to 2*q + (if b='1' then 1 else 0)
    have hb : (if b = '1' then 1 else 0) = m' % 2 := by
      dsimp [b]
      by_cases h : m' % 2 = 1
      · simp [h]
      · simp [h]
    rw [hb]
    -- use div_add_mod to finish
    have : 2 * q + (m' % 2) = m' := by
      -- q is m'/2, so 2*q + m'%2 = m'
      -- Nat.div_add_mod states m' = 2 * (m' / 2) + m' % 2
      exact (Nat.div_add_mod m' 2).symm
    rw [this]
    rfl
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
def ModExp (sx sy sz : String) : String :=
  let n := Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz
  Nat_to_BinString n
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧ Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz
-- </vc-theorem>
-- <vc-proof>
by
  let n := Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz
  have : ModExp sx sy sz = Nat_to_BinString n := rfl
  rw [this]
  constructor
  · exact nat_to_bits_valid_string n
  · exact (Str2Int_nat_to_bits n)
-- </vc-proof>

end BignumLean