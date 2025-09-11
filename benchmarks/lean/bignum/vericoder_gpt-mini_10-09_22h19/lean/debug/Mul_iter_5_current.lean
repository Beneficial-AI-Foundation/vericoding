namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
open WellFounded

namespace Nat
/-- Strong induction for Nat built from well-founded recursion. -/
def strong_induction_on {α : Sort _} (n : Nat) (H : ∀ m, (∀ k, k < m → α) → α) : α :=
  well_founded.fix lt_wf (fun _ => α) (fun m IH => H m (fun k hk => IH k hk)) n
end Nat

-- LLM HELPER
/-- Build binary representation of a natural number as a list of chars '0'/'1'. -/
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
        (ih q (by
          -- prove q < m
          have : q ≠ 0 := by
            intro H; simp [H] at *; contradiction
          -- from q ≠ 0 get 0 < q
          have qpos : 0 < q := by
            apply Nat.pos_of_ne_zero; exact this
          -- q < 2*q < 2*q + (m % 2) = m by div_add_mod
          have : q < 2 * q := by
            calc
              q = 0 + q := by simp
              _ < q + q := by apply Nat.add_lt_add_left; exact qpos
          have : q < 2 * q + (m % 2) := by
            apply Nat.lt_add_of_le_of_pos (Nat.le_refl (2 * q)) (Nat.zero_lt_of_ne_zero (by simp [m % 2] at *))
            -- fallback: use monotonicity
            calc
              q < 2 * q := by
                have qpos' : 0 < q := qpos
                calc
                  q = 0 + q := by simp
                  _ < q + q := by apply Nat.add_lt_add_left; exact qpos'
              _ ≤ 2 * q + (m % 2) := by apply Nat.le_add_right
          -- now we have q < m because m = 2*q + (m % 2)
          have eq := (Nat.div_add_mod m 2).symm
          calc
            q < 2 * q + (m % 2) := this
            _ = m := by rw [eq]
        )) ++ [b]

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
    -- goal becomes: ( ( (foldl tl ...) * 2 + ... ) * 2 + digit ) = foldl (hd :: tl ++ [c]) ...
    -- use ih for tl then simplify
    have : ((tl.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) * 2 +
              (if c = '1' then 1 else 0)) =
           (tl ++ [c]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := ih
    simp [this]
    rfl

-- LLM HELPER
/-- Prove that nat_to_bin_list correctly encodes n as integer via Str2Int. -/
theorem nat_to_bin_list_spec (n : Nat) :
  Str2Int (String.mk (nat_to_bin_list n)) = n := by
  apply Nat.strong_induction_on n; intro m ih
  by_cases hm : m = 0
  · -- m = 0
    simp [hm, nat_to_bin_list, nat_to_bin_string, Str2Int]
    simp [List.foldl]; rfl
  · -- m > 0
    simp [nat_to_bin_list, nat_to_bin_string, hm]
    let q := m / 2
    let b := m % 2
    let bchar := if b = 1 then '1' else '0'
    by_cases hq0 : q = 0
    · -- q = 0 -> m = 1
      have : nat_to_bin_list m = [bchar] := by simp [hq0]
      calc
        Str2Int (String.mk (nat_to_bin_list m)) = Str2Int (String.mk [bchar]) := by simp [this]
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
    · -- q > 0
      have hlist : nat_to_bin_list m = (ih q (by
        -- prove q < m:
        have qpos : 0 < q := by
          have nq : q ≠ 0 := by
            intro H; simp [H] at hq0; contradiction
          exact Nat.pos_of_ne_zero nq
        have : q < 2 * q := by
          calc
            q = 0 + q := by simp
            _ < q + q := by apply Nat.add_lt_add_left; exact qpos
        have : q < 2 * q + (m % 2) := by
          apply Nat.lt_trans this
          apply Nat.le_add_right
        rw [Nat.div_add_mod m 2] at this
      ) : List Char) ++ [bchar] := by simp [hq0]
      calc
        Str2Int (String.mk (nat_to_bin_list m)) =
          Str2Int (String.mk ((ih q (by
            -- same q < m proof as above
            have qpos : 0 < q := by
              have nq : q ≠ 0 := by
                intro H; simp [H] at hq0; contradiction
              exact Nat.pos_of_ne_zero nq
            have : q < 2 * q := by
              calc
                q = 0 + q := by simp
                _ < q + q := by apply Nat.add_lt_add_left; exact qpos
            have : q < 2 * q + (m % 2) := by
              apply Nat.lt_trans this
              apply Nat.le_add_right
            rw [Nat.div_add_mod m 2] at this
          )) ++ [bchar])) := by simp [hlist]
        _ = ( (ih q (by
            have qpos : 0 < q := by
              have nq : q ≠ 0 := by
                intro H; simp [H] at hq0; contradiction
              exact Nat.pos_of_ne_zero nq
            have : q < 2 * q := by
              calc
                q = 0 + q := by simp
                _ < q + q := by apply Nat.add_lt_add_left; exact qpos
            have : q < 2 * q + (m % 2) := by
              apply Nat.lt_trans this
              apply Nat.le_add_right
            rw [Nat.div_add_mod m 2] at this
          ))).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) * 2 +
            (if bchar = '1' then 1 else 0) := by
          -- use foldl append lemma
          have ff := foldl_append_one (ih q (by
            have qpos : 0 < q := by
              have nq : q ≠ 0 := by
                intro H; simp [H] at hq0; contradiction
              exact Nat.pos_of_ne_zero nq
            have : q < 2 * q := by
              calc
                q = 0 + q := by simp
                _ < q + q := by apply Nat.add_lt_add_left; exact qpos
            have : q < 2 * q + (m % 2) := by
              apply Nat.lt_trans this
              apply Nat.le_add_right
            rw [Nat.div_add_mod m 2] at this
          )) bchar
          simp [Str2Int] at ff
          exact ff.symm
        _ = 2 * q + (if bchar = '1' then 1 else 0) := by
          -- apply IH to q: Str2Int (String.mk (nat_to_bin_list q)) = q
          have pref := nat_to_bin_list_spec q
          simp [Str2Int] at pref
          simp [pref]
        _ = 2 * q + b := by
          dsimp [bchar]
          -- show (if bchar = '1' then 1 else 0) = b
          have hb : (if bchar = '1' then 1 else 0) = b := by
            dsimp [
-- </vc-helpers>

-- <vc-spec>
def Mul (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
open WellFounded

namespace Nat
/-- Strong induction for Nat built from well-founded recursion. -/
def strong_induction_on {α : Sort _} (n : Nat) (H : ∀ m, (∀ k, k < m → α) → α) : α :=
  well_founded.fix lt_wf (fun _ => α) (fun m IH => H m (fun k hk => IH k hk)) n
end Nat

-- LLM HELPER
/-- Build binary representation of a natural number as a list of chars '0'/'1'. -/
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
        (ih q (by
          -- prove q < m
          have : q ≠ 0 := by
            intro H; simp [H] at *; contradiction
          -- from q ≠ 0 get 0 < q
          have qpos : 0 < q := by
            apply Nat.pos_of_ne_zero; exact this
          -- q < 2*q < 2*q + (m % 2) = m by div_add_mod
          have : q < 2 * q := by
            calc
              q = 0 + q := by simp
              _ < q + q := by apply Nat.add_lt_add_left; exact qpos
          have : q < 2 * q + (m % 2) := by
            apply Nat.lt_add_of_le_of_pos (Nat.le_refl (2 * q)) (Nat.zero_lt_of_ne_zero (by simp [m % 2] at *))
            -- fallback: use monotonicity
            calc
              q < 2 * q := by
                have qpos' : 0 < q := qpos
                calc
                  q = 0 + q := by simp
                  _ < q + q := by apply Nat.add_lt_add_left; exact qpos'
              _ ≤ 2 * q + (m % 2) := by apply Nat.le_add_right
          -- now we have q < m because m = 2*q + (m % 2)
          have eq := (Nat.div_add_mod m 2).symm
          calc
            q < 2 * q + (m % 2) := this
            _ = m := by rw [eq]
        )) ++ [b]

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
    -- goal becomes: ( ( (foldl tl ...) * 2 + ... ) * 2 + digit ) = foldl (hd :: tl ++ [c]) ...
    -- use ih for tl then simplify
    have : ((tl.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) * 2 +
              (if c = '1' then 1 else 0)) =
           (tl ++ [c]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := ih
    simp [this]
    rfl

-- LLM HELPER
/-- Prove that nat_to_bin_list correctly encodes n as integer via Str2Int. -/
theorem nat_to_bin_list_spec (n : Nat) :
  Str2Int (String.mk (nat_to_bin_list n)) = n := by
  apply Nat.strong_induction_on n; intro m ih
  by_cases hm : m = 0
  · -- m = 0
    simp [hm, nat_to_bin_list, nat_to_bin_string, Str2Int]
    simp [List.foldl]; rfl
  · -- m > 0
    simp [nat_to_bin_list, nat_to_bin_string, hm]
    let q := m / 2
    let b := m % 2
    let bchar := if b = 1 then '1' else '0'
    by_cases hq0 : q = 0
    · -- q = 0 -> m = 1
      have : nat_to_bin_list m = [bchar] := by simp [hq0]
      calc
        Str2Int (String.mk (nat_to_bin_list m)) = Str2Int (String.mk [bchar]) := by simp [this]
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
    · -- q > 0
      have hlist : nat_to_bin_list m = (ih q (by
        -- prove q < m:
        have qpos : 0 < q := by
          have nq : q ≠ 0 := by
            intro H; simp [H] at hq0; contradiction
          exact Nat.pos_of_ne_zero nq
        have : q < 2 * q := by
          calc
            q = 0 + q := by simp
            _ < q + q := by apply Nat.add_lt_add_left; exact qpos
        have : q < 2 * q + (m % 2) := by
          apply Nat.lt_trans this
          apply Nat.le_add_right
        rw [Nat.div_add_mod m 2] at this
      ) : List Char) ++ [bchar] := by simp [hq0]
      calc
        Str2Int (String.mk (nat_to_bin_list m)) =
          Str2Int (String.mk ((ih q (by
            -- same q < m proof as above
            have qpos : 0 < q := by
              have nq : q ≠ 0 := by
                intro H; simp [H] at hq0; contradiction
              exact Nat.pos_of_ne_zero nq
            have : q < 2 * q := by
              calc
                q = 0 + q := by simp
                _ < q + q := by apply Nat.add_lt_add_left; exact qpos
            have : q < 2 * q + (m % 2) := by
              apply Nat.lt_trans this
              apply Nat.le_add_right
            rw [Nat.div_add_mod m 2] at this
          )) ++ [bchar])) := by simp [hlist]
        _ = ( (ih q (by
            have qpos : 0 < q := by
              have nq : q ≠ 0 := by
                intro H; simp [H] at hq0; contradiction
              exact Nat.pos_of_ne_zero nq
            have : q < 2 * q := by
              calc
                q = 0 + q := by simp
                _ < q + q := by apply Nat.add_lt_add_left; exact qpos
            have : q < 2 * q + (m % 2) := by
              apply Nat.lt_trans this
              apply Nat.le_add_right
            rw [Nat.div_add_mod m 2] at this
          ))).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) * 2 +
            (if bchar = '1' then 1 else 0) := by
          -- use foldl append lemma
          have ff := foldl_append_one (ih q (by
            have qpos : 0 < q := by
              have nq : q ≠ 0 := by
                intro H; simp [H] at hq0; contradiction
              exact Nat.pos_of_ne_zero nq
            have : q < 2 * q := by
              calc
                q = 0 + q := by simp
                _ < q + q := by apply Nat.add_lt_add_left; exact qpos
            have : q < 2 * q + (m % 2) := by
              apply Nat.lt_trans this
              apply Nat.le_add_right
            rw [Nat.div_add_mod m 2] at this
          )) bchar
          simp [Str2Int] at ff
          exact ff.symm
        _ = 2 * q + (if bchar = '1' then 1 else 0) := by
          -- apply IH to q: Str2Int (String.mk (nat_to_bin_list q)) = q
          have pref := nat_to_bin_list_spec q
          simp [Str2Int] at pref
          simp [pref]
        _ = 2 * q + b := by
          dsimp [bchar]
          -- show (if bchar = '1' then 1 else 0) = b
          have hb : (if bchar = '1' then 1 else 0) = b := by
            dsimp [
-- </vc-code>

end BignumLean