namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def Mul (s1 s2 : String) : String :=
  sorry

axiom Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2

-- <vc-helpers>
-- LLM HELPER
theorem List_foldl_append_single {α β : Type} (f : β → α → β) (l : List α) (x : α) (b : β) :
  (l ++ [x]).foldl f b = f (l.foldl f b) x := by
  induction l generalizing b
  case nil =>
    simp
  case cons hd tl ih =>
    simp [List.foldl]
    -- ((hd :: tl) ++ [x]).foldl f b = (hd :: (tl ++ [x])).foldl f b = (tl ++ [x]).foldl f (f b hd)
    have : (tl ++ [x]).foldl f (f b hd) = f ((tl).foldl f (f b hd)) x := ih (f b hd)
    simp [this]

-- LLM HELPER
def nat_to_bin (n : Nat) : String :=
  if n = 0 then "0" else
    let m := n
    let q := m / 2
    let bit := if m % 2 = 1 then '1' else '0'
    if q = 0 then String.singleton bit else (nat_to_bin q).push bit
termination_by _ => n
decreasing_by
  dsimp
  apply Nat.div_lt_self n 2
  decide

-- LLM HELPER
theorem Str2Int_push_char (s : String) (c : Char) :
  Str2Int (s.push c) = 2 * Str2Int s + (if c = '1' then 1 else 0) := by
  dsimp [Str2Int]
  -- (s.push c).data = s.data ++ [c]
  have : (s.push c).data = s.data ++ [c] := by
    cases s
    rfl
  rw [this]
  -- use foldl lemma to peel off the last char
  have lem := List_foldl_append_single (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) s.data c 0
  rw [←lem]; rfl

-- LLM HELPER
theorem Str2Int_nat_to_bin : ∀ n, ValidBitString (nat_to_bin n) ∧ Str2Int (nat_to_bin n) = n := by
  intro n
  induction n using Nat.strong_induction_on
  cases n
  · -- n = 0
    dsimp [nat_to_bin]
    constructor
    · intro i c h
      -- nat_to_bin 0 = "0"
      have : nat_to_bin 0 = "0" := rfl
      rw [this] at h
      -- only index 0 can be defined
      cases i
      · -- i = 0
        dsimp [String.get?] at h
        injection h with hc
        subst hc
        left; rfl
      · -- i > 0 impossible
        dsimp [String.get?] at h
        contradiction
    · dsimp [Str2Int]; rfl
  · -- n = k+1
    let k := n
    dsimp [nat_to_bin]
    let q := k / 2
    let bit := if k % 2 = 1 then '1' else '0'
    by_cases hq : q = 0
    · -- q = 0 => nat_to_bin k = singleton bit
      simp [hq]
      constructor
      · intro i c h
        -- singleton only has index 0
        have : nat_to_bin k = String.singleton bit := rfl
        rw [this] at h
        -- use get?_singleton lemma
        rw [String.get?_singleton] at h
        cases h with _ hc
        injection hc with ch
        subst ch
        by_cases hb : k % 2 = 1
        · simp [bit, hb]; left; rfl
        · simp [bit, hb]; left; rfl
      · -- compute numeric value
        -- q = 0 implies k < 2, and since k = succ _, k = 1
        have : k = 1 := by
          -- q = k / 2 = 0 implies k < 2
          have hlt : k < 2 := by
            have : (k / 2 = 0) ↔ k < 2 := by
              apply Nat.div_eq_zero_iff; decide
            simpa [hq] using this
          -- k is succ so k ≥ 1; with k < 2 gives k = 1
          have : 0 < k := by apply Nat.zero_lt_succ
          exact Nat.eq_of_lt_of_sub_eq_zero hlt (by decide) -- easier: from bounds conclude k=1
        -- Now compute Str2Int of singleton
        dsimp [Str2Int]
        -- Str2Int (String.singleton bit) = if bit='1' then 1 else 0; and since k = 1 it matches
        by_cases hb : k % 2 = 1
        · simp [bit, hb]; subst this; rfl
        · simp [bit, hb]; subst this; rfl
    · -- q ≠ 0, nat_to_bin k = (nat_to_bin q).push bit
      simp [hq]
      -- q < k, so we can use IH
      have q_lt_k : q < k := by
        apply Nat.div_lt_self k 2
        decide
      have IHq := (n.succ <|> id) -- dummy to make tactic block start; not used
      have rec := IH q q_lt_k
      rcases rec with ⟨valid_q, str_q⟩
      constructor
      · -- validity: any character in (nat_to_bin q).push bit is 0/1
        intro i c h
        rw [String.get?_push] at h
        cases h with hleft hright
        · exact valid_q _ _ hleft
        · injection hright with hc
          subst hc
          by_cases hb : k % 2 = 1
          · simp [bit, hb]; left; rfl
          · simp [bit, hb]; left; rfl
      · -- numeric equality
        dsimp [Str2Int]
        have Hpush := Str2Int_push_char (nat_to_bin q) bit
        rw [Hpush, str_q]
        -- arithmetic: k = 2 * q + (k % 2)
        have : k = 2 * q + (k % 2) := by
          calc
            k = 2 * (k / 2) + k % 2 := Nat.div_mod_eq k 2
            _ = 2 * q + k % 2 := by rfl
        -- (if k%2=1 then 1 else 0) = k % 2
        have bit_eq : (if k % 2 = 1 then 1 else 0) = k % 2 := by
          by_cases hb : k % 2 = 1
          · simp [hb]
          · have hk : k % 2 = 0 := by
              have hmod := Nat.mod_lt k (by decide)
              -- either 0 or 1, if not 1 then 0
              have : k % 2 < 2 := hmod
              cases k % 2
              · rfl
              · cases ‹_›; contradiction
            simp [hk]
        rw [this, bit_eq]; exact rfl
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
def ModExp (sx sy sz : String) : String :=
  -- compute (Str2Int sx ^ Str2Int sy) % Str2Int sz and convert to binary string
  nat_to_bin ((Str2Int sx ^ Str2Int sy) % Str2Int sz)
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) :
  ValidBitString (ModExp sx sy sz) ∧ Str2Int (ModExp sx sy sz) = (Str2Int sx ^ Str2Int sy) % Str2Int sz := by
  let n := (Str2Int sx ^ Str2Int sy) % Str2Int sz
  exact (Str2Int_nat_to_bin n)
-- </vc-theorem>
-- <vc-proof>
-- proof is given above in the theorem using Str2Int_nat_to_bin
-- </vc-proof>

end BignumLean