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
  -- show (k+1)/2 < k+1
  dsimp [Nat.div]
  apply Nat.div_lt_self
  · exact Nat.succ_pos k
  · decide

-- LLM HELPER
def Nat_to_BinString (n : Nat) : String :=
  String.mk (nat_to_bits n)

-- LLM HELPER
theorem get?_mem {α : Type _} : ∀ (l : List α) (i : Nat) (x : α), l.get? i = some x -> x ∈ l := by
  intro l i x h
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
      exact ih _ h

-- LLM HELPER
theorem nat_to_bits_members (n : Nat) :
  ∀ {c}, c ∈ nat_to_bits n → (c = '0' ∨ c = '1') := by
  apply Nat.strong_induction_on n
  intro n ih
  cases n with
  | zero =>
    intro c h
    simp [nat_to_bits] at h
    cases h
    · simp_all
    · contradiction
  | succ k =>
    intro c h
    simp [nat_to_bits]
    let k' := k + 1
    let m := k' / 2
    let b := if k' % 2 = 1 then '1' else '0'
    have H : nat_to_bits k' = nat_to_bits m ++ [b] := rfl
    rw [H] at h
    have hh := List.mem_append.1 h
    cases hh with
    | inl hin =>
      -- element from left part, use induction hypothesis on m
      have m_lt : m < k' := by
        apply Nat.div_lt_self
        · exact Nat.succ_pos k
        · decide
      apply (ih m m_lt)
      exact hin
    | inr hin =>
      -- element is the last element [b]
      simp at hin
      injection hin with hc
      rw [hc]
      simp [b]
      -- if-then-else yields either '1' or '0'
      by_cases hmod : k' % 2 = 1
      · simp [hmod]; right; rfl
      · simp [hmod]; left; rfl

-- LLM HELPER
theorem nat_to_bits_valid_string (n : Nat) :
  ValidBitString (Nat_to_BinString n) := by
  intro i c h
  simp [Nat_to_BinString] at h
  -- underlying list get? yields membership
  have : c ∈ nat_to_bits n := by
    -- convert String.get? to List.get? on underlying list
    -- String.get? i = some c gives (nat_to_bits n).get? i = some c
    -- so we use get?_mem lemma
    have : (nat_to_bits n).get? i = some c := h
    exact (get?_mem (nat_to_bits n) i c this)
  apply nat_to_bits_members n
  exact this

-- LLM HELPER
theorem Str2Int_nat_to_bits (n : Nat) :
  Str2Int (Nat_to_BinString n) = n := by
  apply Nat.strong_induction_on n
  intro n ih
  cases n with
  | zero =>
    simp [Nat_to_BinString, nat_to_bits, Str2Int]
    -- ['0'] foldl gives 0
    rfl
  | succ k =>
    let k' := k + 1
    let m := k' / 2
    let b := if k' % 2 = 1 then '1' else '0'
    have H : nat_to_bits k' = nat_to_bits m ++ [b] := rfl
    simp [Nat_to_BinString, Str2Int, H]
    -- foldl append lemma
    have foldl_append := List.foldl_append (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 (nat_to_bits m) [b]
    rw [foldl_append]
    -- compute foldl over single element [b]
    simp
    have ih_m : Str2Int (Nat_to_BinString m) = m := (ih m) (by
      have : m < k' := by
        apply Nat.div_lt_self
        · exact Nat.succ_pos k
        · decide
      exact this)
    -- foldl over nat_to_bits m equals m by definition of Str2Int and ih_m
    have : (nat_to_bits m).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = m := by
      simp [Str2Int, Nat_to_BinString] at ih_m
      exact ih_m
    rw [this]
    -- now conclude value is 2*m + (if b='1' then 1 else 0) which is k'
    have hb : (if b = '1' then 1 else 0) = k' % 2 := by
      dsimp [b]
      by_cases h : k' % 2 = 1
      · simp [h]
      · simp [h]
    rw [hb]
    -- use div_add_mod
    have := Nat.div_add_mod k' 2
    -- div_add_mod states k' = 2 * (k' / 2) + (k' % 2)
    -- rewrite 2 * (k'/2) as 2*m since m = k'/2
    have : 2 * m + (k' % 2) = k' := by
      simp [m]
      exact Nat.div_add_mod k' 2
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
proof
  -- Unfold ModExp and apply lemmas about Nat_to_BinString
  let n := Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz
  have : ModExp sx sy sz = Nat_to_BinString n := rfl
  rw [this]
  constructor
  · exact nat_to_bits_valid_string n
  · exact (Str2Int_nat_to_bits n)
end
-- </vc-proof>

end BignumLean