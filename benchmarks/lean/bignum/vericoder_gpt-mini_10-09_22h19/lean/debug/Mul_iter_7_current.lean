namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
open WellFounded

namespace Nat

/-- Strong induction principle for Nat. -/
theorem strong_induction_on {P : Nat → Prop} (n : Nat) (H : ∀ m, (∀ k, k < m → P k) → P m) : P n := by
  apply WellFounded.induction lt_wf n
  intro m ih
  apply H m
  intro k hk
  exact ih k hk

end Nat

-- LLM HELPER
/-- Build binary representation of a natural number as a list of chars '0'/'1'. -/
def nat_to_bin_list : Nat → List Char := fun n =>
  WellFounded.fix lt_wf (fun _ => List Char) fun m rec =>
    if m = 0 then
      ['0']
    else
      let q := m / 2
      let b := if m % 2 = 1 then '1' else '0'
      if q = 0 then
        [b]
      else
        rec q (by
          -- prove q < m
          have nq : q ≠ 0 := by
            intro H; simp [H] at *; contradiction
          have qpos : 0 < q := by
            exact Nat.pos_of_ne_zero nq
          have : q < 2 * q := by
            calc
              q = 0 + q := by simp
              _ < q + q := by apply Nat.add_lt_add_left; exact qpos
          have : q < 2 * q + (m % 2) := by
            apply Nat.lt_trans this
            apply Nat.le_add_right
          rw [Nat.div_add_mod m 2] at this
          exact this) ++ [b]

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
      have nq : q ≠ 0 := by intro H; simp [H] at hq0; contradiction
      have qpos : 0 < q := by exact Nat.pos_of_ne_zero nq
      have qltm : q < m := by
        have : q < 2 * q := by
          calc
            q = 0 + q := by simp
            _ < q + q := by apply Nat.add_lt_add_left; exact qpos
        have : q < 2 * q + (m % 2) := by
          apply Nat.lt_trans this
          apply Nat.le_add_right
        rw [Nat.div_add_mod m 2] at this
        exact this
      have hlist : nat_to_bin_list m = ( (WellFounded.fix lt_wf (fun _ => List Char) fun (x : Nat) rec => 
                        if x = 0 then ['0'] else
                          let qx := x / 2
                          let bx := if x % 2 = 1 then '1' else '0'
                          if qx = 0 then [bx] else rec qx (by
                            have nq : qx ≠ 0 := by intro H; simp [H] at *; contradiction
                            have qpos : 0 < qx := by exact Nat.pos_of_ne_zero nq
                            have : qx < 2 * qx := by
                              calc
                                qx = 0 + qx := by simp
                                _ < qx + qx := by apply Nat.add_lt_add_left; exact qpos
                            have : qx < 2 * qx + (x % 2) := by
                              apply Nat.lt_trans this
                              apply Nat.le_add_right
                            rw [Nat.div_add_mod x 2] at this
                            exact this) ++ [bx]) m := by simp [hq0]
      -- Use IH on q
      have ihq := ih q fun k hk => ih k hk
      calc
        Str2Int (String.mk (nat_to_bin_list m)) =
          Str2Int (String.mk ((ih q (fun k hk => ih k hk)) ++ [bchar])) := by
            simp [hlist]
        _ = ((ih q (fun k hk => ih k hk)).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) * 2 +
              (if bchar = '1' then 1 else 0) := by
            have ff := foldl_append_one (ih q (fun k hk => ih k hk)) bchar
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
          have hb : (if bchar = '1' then 1 else 0) = (if b = 1 then 1 else 0) := by dsimp [bchar]; rfl
          have : (if b = 1 then 1 else 0) = b := by
            -- b = m % 2, so b < 2; hence b is 0 or 1
            have b_lt2 : b < 2 := Nat.mod_lt m (by norm_num)
            cases b with
            | zero => simp
            | succ b' =>
              cases b' with
              | zero => simp
              | succ _ => linarith [b_lt2]
          calc
            (if bchar = '1' then 1 else 0) = (if b = 1 then 1 else 0) := by exact hb
            _ = b := by exact this
-- end helpers
-- </vc-helpers>

-- <vc-spec>
def Mul (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
def Mul (s1 s2 : String) : String :=
  let n1 := Str2Int s1
  let n2 := Str2Int s2
  nat_to_bin_string (n1 * n2)
-- </vc-code>

-- <vc-theorem>
theorem Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2
-- </vc-theorem>
-- <vc-proof>
by
  dsimp [Mul, nat_to_bin_string]
  -- Mul s1 s2 = nat_to_bin_string (Str2Int s1 * Str2Int s2)
  apply nat_to_bin_list_spec
-- </vc-proof>

end BignumLean