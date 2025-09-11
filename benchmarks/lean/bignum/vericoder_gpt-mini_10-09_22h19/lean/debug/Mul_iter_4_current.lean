namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
open WellFounded

/-
Provide a basic strong_induction_on for Nat using well-founded recursion.
This recreates the common Nat.strong_induction_on facility so proofs below can use it.
-/
namespace Nat
def strong_induction_on {α : Sort _} (n : Nat) (H : ∀ m, (∀ k, k < m → α) → α) : α :=
  well_founded.fix lt_wf (fun _ => α) (fun m IH => H m (fun k hk => IH k hk)) n
end Nat

-- LLM HELPER
/-
Construct binary representation of a natural number as a list of '0'/'1' chars.
We build it using strong induction so termination is clear.
-/
def nat_to_bin_list (n : Nat) : List Char :=
  Nat.strong_induction_on n fun m ih =>
    if m = 0 then
      ['0']
    else
      let q := m / 2
      let b := if m % 2 = 1 then '1' else '0'
      if q = 0 then
        [b]
      else
        -- use the induction hypothesis on q (which is < m by div_lt_self)
        (ih q (by apply Nat.div_lt_self; decide)) ++ [b]

-- LLM HELPER
def nat_to_bin_string (n : Nat) : String := String.mk (nat_to_bin_list n)

-- LLM HELPER
theorem nat_to_bin_list_spec (n : Nat) :
  Str2Int (String.mk (nat_to_bin_list n)) = n := by
  apply Nat.strong_induction_on n; intro m ih
  by_cases hm : m = 0
  · -- m = 0
    simp [hm, nat_to_bin_list, nat_to_bin_string, Str2Int]
    -- foldl over ['0'] yields 0
    simp [List.foldl]; rfl
  · -- m > 0
    simp [nat_to_bin_list, nat_to_bin_string, hm]
    let q := m / 2
    let b := m % 2
    let bchar := if b = 1 then '1' else '0'
    -- handle q = 0 separately (this is the case m = 1)
    by_cases hq0 : q = 0
    · -- q = 0 so m = 1
      have : nat_to_bin_list m = [bchar] := by simp [hq0]
      calc
        Str2Int (String.mk (nat_to_bin_list m)) = Str2Int (String.mk [bchar]) := by simp [this]
        _ = (if bchar = '1' then 1 else 0) := by simp [Str2Int]; rfl
        _ = b := by
          -- when q = 0 and m > 0, m = 1 so b = 1
          have : m = 1 := by
            have : m = 2 * q + b := by simp [q, b]; apply (Nat.div_add_mod m 2).symm
            simp [hq0] at this; exact this
          subst this
          simp [b]; rfl
        _ = m := by
          have : m = 2 * q + b := by simp [q, b]; apply (Nat.div_add_mod m 2).symm
          simp [hq0] at this; simp at this; exact this.symm
    · -- q > 0
      -- nat_to_bin_list m = (nat_to_bin_list q) ++ [bchar]
      have hlist : nat_to_bin_list m = (ih q (by apply Nat.div_lt_self; decide)) ++ [bchar] := by
        simp [hq0]
      calc
        Str2Int (String.mk (nat_to_bin_list m)) =
          Str2Int (String.mk ((ih q (by apply Nat.div_lt_self; decide)) ++ [bchar])) := by simp [hlist]
        _ = (List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 (ih q (by apply Nat.div_lt_self; decide))) * 2 +
            (if bchar = '1' then 1 else 0) := by
          -- foldl over (l ++ [ch]) equals 2 * (foldl over l) + digit
          have := List.foldl_append (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 (ih q (by apply Nat.div_lt_self; decide)) [bchar]
          simp [Str2Int] at this
          exact this
        _ = 2 * q + (if bchar = '1' then 1 else 0) := by
          -- apply IH to q to get foldl value = q
          have pref := nat_to_bin_list_spec q
          -- pref states Str2Int (String.mk (nat_to_bin_list q)) = q
          -- unfold Str2Int to foldl
          simp [Str2Int] at pref
          -- rewrite the foldl part
          simp [pref]
        _ = 2 * q + b := by
          -- show (if bchar = '1' then 1 else 0) = b
          have hb : (if bchar = '1' then 1 else 0) = b := by
            dsimp [bchar]
            -- b is 0 or 1
            have brange : b = 0 ∨ b = 1 := by
              cases b <;> simp [b]; try linarith; exact Or.inr rfl
            cases brange
            · subst brange; simp
            · subst brange; simp
          exact hb.symm
        _ = m := by
          -- m = 2*q + b
          have := Nat.div_add_mod m 2
          simp [q, b] at this
          exact this.symm

-- LLM HELPER
theorem nat_to_bin_list_valid (n : Nat) : ValidBitString (String.mk (nat_to_bin_list n)) := by
  unfold ValidBitString
  intro i c h
  -- convert String.get? to List.get?
  simp [String.get?] at h
  -- prove that every character in nat_to_bin_list n is '0' or '1'
  have all_chars : (nat_to_bin_list n).all (fun ch => ch = '0' ∨ ch = '1') := by
    apply Nat.strong_induction_on n; intro m ih
    by_cases hm : m = 0
    · simp [hm, nat_to_bin_list]
    · -- m > 0
      simp [nat_to_bin_list, hm]
      let q := m / 2
      let b := if m % 2 = 1 then '1' else '0'
      by_cases hq0 : q = 0
      · simp [hq0]
      · -- q > 0, use IH for q
        have pref := ih q (by apply Nat.div_lt_self; decide)
        simp [pref]
        -- pref yields that the prefix list has the property; appending b preserves it
        apply List.all_append.2
        constructor
        · exact pref
        · simp [b]
  -- now from (nat_to_bin_list n).get? i = some c deduce c ∈ list
  have mem : c ∈ (nat_to_bin_list n) := by
    -- use List.get?_mem: l.get? i = some a -> a ∈ l
    exact (List.get?_mem.1 h)
  -- from all_chars and membership deduce property for c
  exact List.all_mem.2 all_chars mem
-- </vc-helpers>

-- <vc-spec>
def Mul (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
def Mul (s1 s2 : String) : String :=
  nat_to_bin_string (Str2Int s1 * Str2Int s2)
-- </vc-code>

-- <vc-theorem>
theorem Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2 := by
  -- Mul is defined via nat_to_bin_string on the product
  simp [Mul, nat_to_bin_string]
  apply And.intro
  · -- validity: nat_to_bin_string produces valid bitstrings for any Nat
    apply nat_to_bin_list_valid
  · -- numeric equality: nat_to_bin_string encodes numbers correctly
    apply nat_to_bin_list_spec
-- </vc-theorem>
-- <vc-proof>
-- All required proofs are provided in the helpers and theorem sections above.
-- No additional proofs required here.
-- </vc-proof>

end BignumLean