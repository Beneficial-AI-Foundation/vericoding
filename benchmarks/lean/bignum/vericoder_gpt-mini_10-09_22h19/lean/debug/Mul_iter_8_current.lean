namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
open WellFounded

namespace Nat

/-- Strong induction principle for Nat (built from a measure well-founded relation). -/
theorem strong_induction_on {P : Nat → Prop} (n : Nat)
  (H : ∀ m, (∀ k, k < m → P k) → P m) : P n := by
  apply WellFounded.induction (WellFounded.measure_wf fun x => x) n
  intro m ih
  apply H m
  intro k hk
  exact ih k hk

end Nat

-- LLM HELPER
/-- Build binary representation of a natural number as a list of chars '0'/'1'. -/
def nat_to_bin_list : Nat → List Char :=
  WellFounded.fix (WellFounded.measure_wf fun x => x) (fun _ => List Char) fun m rec =>
    if m = 0 then
      ['0']
    else
      let q := m / 2
      let b := if m % 2 = 1 then '1' else '0'
      if q = 0 then
        [b]
      else
        rec q (by
          -- prove q < m using division lemma: for b = 2 we have m / 2 < m
          have : 1 < 2 := by norm_num
          exact Nat.div_lt_self (m := m) (b := 2) this) ++ [b]

-- LLM HELPER
def nat_to_bin_string (n : Nat) : String := String.mk (nat_to_bin_list n)

-- LLM HELPER
/-- Helper: foldl property for our specific binary-accumulating function when appending one digit. -/
theorem foldl_append_one (l : List Char) (c : Char) :
    (l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) * 2 +
      (if c = '1' then 1 else 0) =
    (l ++ [c]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
  induction l with
  | nil =>
    simp [List.foldl]
  | cons hd tl ih =>
    simp [List.foldl]
    have : ((tl.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) * 2 +
              (if c = '1' then 1 else 0)) =
           (tl ++ [c]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := ih
    simp [this]
    rfl

-- LLM HELPER
/-- Prove that nat_to_bin_list correctly encodes n as integer via Str2Int. -/
theorem nat_to_bin_list_spec (n : Nat) :
  Str2Int (String.mk (nat_to_bin_list n)) = n := by
  apply Nat.strong_induction_on n
  intro m ih
  by_cases hm : m = 0
  · -- m = 0
    simp [hm, nat_to_bin_list, nat_to_bin_string, Str2Int, List.foldl]
  · -- m > 0
    -- unfold definition
    have mpos : 0 < m := by
      apply Nat.pos_of_ne_zero
      intro H; simp [H] at hm; contradiction
    simp [nat_to_bin_list] at *
    let q := m / 2
    let b := m % 2
    let bchar := if b = 1 then '1' else '0'
    by_cases hq0 : q = 0
    · -- q = 0 -> m = 1
      have hdef : nat_to_bin_list m = [bchar] := by
        simp [hm, hq0]
      calc
        Str2Int (String.mk (nat_to_bin_list m)) = Str2Int (String.mk [bchar]) := by simp [hdef]
        _ = (if bchar = '1' then 1 else 0) := by simp [Str2Int]; rfl
        _ = b := by
          dsimp [bchar]
          -- when q = 0 and m > 0, m = 1 so b = 1
          have m_eq : m = 1 := by
            have eq := (Nat.div_add_mod m 2).symm
            simp [hq0] at eq
            exact eq
          subst m_eq
          simp [b]; rfl
        _ = m := by
          have eq := (Nat.div_add_mod m 2).symm
          simp [hq0] at eq
          simp [eq]
    · --
-- </vc-helpers>

-- <vc-spec>
def Mul (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
open WellFounded

namespace Nat

/-- Strong induction principle for Nat (built from a measure well-founded relation). -/
theorem strong_induction_on {P : Nat → Prop} (n : Nat)
  (H : ∀ m, (∀ k, k < m → P k) → P m) : P n := by
  apply WellFounded.induction (WellFounded.measure_wf fun x => x) n
  intro m ih
  apply H m
  intro k hk
  exact ih k hk

end Nat

-- LLM HELPER
/-- Build binary representation of a natural number as a list of chars '0'/'1'. -/
def nat_to_bin_list : Nat → List Char :=
  WellFounded.fix (WellFounded.measure_wf fun x => x) (fun _ => List Char) fun m rec =>
    if m = 0 then
      ['0']
    else
      let q := m / 2
      let b := if m % 2 = 1 then '1' else '0'
      if q = 0 then
        [b]
      else
        rec q (by
          -- prove q < m using division lemma: for b = 2 we have m / 2 < m
          have : 1 < 2 := by norm_num
          exact Nat.div_lt_self (m := m) (b := 2) this) ++ [b]

-- LLM HELPER
def nat_to_bin_string (n : Nat) : String := String.mk (nat_to_bin_list n)

-- LLM HELPER
/-- Helper: foldl property for our specific binary-accumulating function when appending one digit. -/
theorem foldl_append_one (l : List Char) (c : Char) :
    (l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) * 2 +
      (if c = '1' then 1 else 0) =
    (l ++ [c]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
  induction l with
  | nil =>
    simp [List.foldl]
  | cons hd tl ih =>
    simp [List.foldl]
    have : ((tl.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) * 2 +
              (if c = '1' then 1 else 0)) =
           (tl ++ [c]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := ih
    simp [this]
    rfl

-- LLM HELPER
/-- Prove that nat_to_bin_list correctly encodes n as integer via Str2Int. -/
theorem nat_to_bin_list_spec (n : Nat) :
  Str2Int (String.mk (nat_to_bin_list n)) = n := by
  apply Nat.strong_induction_on n
  intro m ih
  by_cases hm : m = 0
  · -- m = 0
    simp [hm, nat_to_bin_list, nat_to_bin_string, Str2Int, List.foldl]
  · -- m > 0
    -- unfold definition
    have mpos : 0 < m := by
      apply Nat.pos_of_ne_zero
      intro H; simp [H] at hm; contradiction
    simp [nat_to_bin_list] at *
    let q := m / 2
    let b := m % 2
    let bchar := if b = 1 then '1' else '0'
    by_cases hq0 : q = 0
    · -- q = 0 -> m = 1
      have hdef : nat_to_bin_list m = [bchar] := by
        simp [hm, hq0]
      calc
        Str2Int (String.mk (nat_to_bin_list m)) = Str2Int (String.mk [bchar]) := by simp [hdef]
        _ = (if bchar = '1' then 1 else 0) := by simp [Str2Int]; rfl
        _ = b := by
          dsimp [bchar]
          -- when q = 0 and m > 0, m = 1 so b = 1
          have m_eq : m = 1 := by
            have eq := (Nat.div_add_mod m 2).symm
            simp [hq0] at eq
            exact eq
          subst m_eq
          simp [b]; rfl
        _ = m := by
          have eq := (Nat.div_add_mod m 2).symm
          simp [hq0] at eq
          simp [eq]
    · --
-- </vc-code>

end BignumLean