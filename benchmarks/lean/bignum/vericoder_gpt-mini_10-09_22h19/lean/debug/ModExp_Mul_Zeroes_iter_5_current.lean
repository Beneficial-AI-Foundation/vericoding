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

-- LLM HELPER
def Nat_to_BinString (n : Nat) : String :=
  String.mk (nat_to_bits n)

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
    · simp [*]
    · contradiction
  | succ k =>
    intro c h
    simp [nat_to_bits] at h
    let m := (k+1) / 2
    let b := if (k+1) % 2 = 1 then '1' else '0'
    have : nat_to_bits m ++ [b] = nat_to_bits (k+1) := rfl
    rw [this] at h
    apply List.mem_append.1 h
    intro h'
    cases h' with
    | inl hleft =>
      -- element comes from nat_to_bits m, and m < k+1 so we can use ih
      apply (ih m)
      . apply Nat.div_lt_self (by linarith) (by decide) -- m < k+1
      . assumption
    | inr hright =>
      simp at hright
      injection hright with hc
      rw [hc]
      simp [b]
      apply Or.inr <| by
        cases (Decidable.eq ((k+1) % 2) 1) with
        | isTrue _ => rfl
        | isFalse _ => rfl

-- LLM HELPER
theorem nat_to_bits_valid_string (n : Nat) :
  ValidBitString (Nat_to_BinString n) := by
  intro i c h
  simp [Nat_to_BinString] at h
  -- h : (nat_to_bits n).get? i = some c
  -- From get? we know c ∈ nat_to_bits n
  have : c ∈ nat_to_bits n := by
    -- List.get?_mem: if get? returns some c then c is in list
    -- Prove by case analysis on i
    induction i with
    | zero =>
      simp at h
      cases h; -- either head or false
      · left; rfl
      · contradiction
    | succ i' =>
      -- general fact: if l.get? (i'+1) = some c then c ∈ l
      -- use List.get?_eq_none / List.get?_some lemmas indirectly:
      -- we can proceed by using List.get?_eq_get? and then mem property
      -- Simpler: use List.get?_mem lemma via rewriting get? as List.get? on underlying list
      -- Here we can reason by induction on list length; but easier: use this known lemma:
      -- If l.get? (i+1) = some c then c ∈ l
      -- We'll prove by constructing membership via List.get?_append/internals:
      revert h
      induction n with
      | zero => simp [nat_to_bits] at h; contradiction
      | succ k =>
        simp [nat_to_bits] at h
        let m := (k+1)/2
        let b := if (k+1) % 2 = 1 then '1' else '0'
        have : nat_to_bits m ++ [b] = nat_to_bits (k+1) := rfl
        rw [this] at h
        apply List.get?_mem_append.1 h
  -- now use previous lemma to conclude character is '0' or '1'
  apply nat_to_bits_members
  apply this

-- LLM HELPER
theorem Str2Int_nat_to_bits (n : Nat) :
  Str2Int (Nat_to_BinString n) = n := by
  -- Prove by strong induction on n
  apply Nat.strong_induction_on n
  intro n ih
  cases n with
  | zero =>
    simp [Nat_to_BinString, nat_to_bits, Str2Int]
    -- ['0'] foldl gives 0
    rfl
  | succ k =>
    -- let k' = k+1
    let k' := k+1
    let m := k' / 2
    let b := if k' % 2 = 1 then '1' else '0'
    have H : nat_to_bits k' = nat_to_bits m ++ [b] := rfl
    simp [Nat_to_BinString, H, Str2Int]
    -- Str2Int of appended list: (nat_to_bits m ++ [b]).foldl f 0 =
    -- (=) List.foldl_append ... gives [b].foldl f (foldl nat_to_bits m 0) = f (foldl nat_to_bits m 0) b
    have foldl_append := List.foldl_append (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 (nat_to_bits m) [b]
    -- compute foldl on single element [b]
    rw [foldl_append]
    simp
    have ih_m : Str2Int (Nat_to_BinString m) = m := (ih m) (by
      show m < k'
      apply Nat.div_lt_self
      · linarith
      · decide)
    -- foldl over nat_to_bits m equals m by definition of Str2Int and ih_m
    have : (nat_to_bits m).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = m := by
      simp [Str2Int, Nat_to_BinString] at ih_m
      exact ih_m
    -- now conclude value is 2*m + (if b='1' then 1 else 0) which is k'
    have : 2 * m + (if b = '1' then 1 else 0) = k' := by
      -- b encodes k' % 2, so RHS is 2*(k'/2) + k' % 2 = k'
      have hb : (if b = '1' then 1 else 0) = k' % 2 := by
        dsimp [b]
        by_cases h : k' % 2 = 1
        · simp [h]
        · simp [h]
      rw [hb]
      exact Nat.div_add_mod k' 2
    -- finish
    simp [this] at *
    rw [this]
    done
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
-- </vc-theorem>
end BignumLean