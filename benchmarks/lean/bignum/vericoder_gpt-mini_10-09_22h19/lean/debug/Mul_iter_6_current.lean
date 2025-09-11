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
          have nq : q ≠ 0 := by
            intro H; simp [H] at *; contradiction
          have qpos : 0 < q := by
            apply Nat.pos_of_ne_zero; exact nq
          have : q < 2 * q := by
            calc
              q = 0 + q := by simp
              _ < q + q := by apply Nat.add_lt_add_left; exact qpos
          have : q < 2 * q + (m % 2) := by
            apply Nat.lt_trans this
            apply Nat.le_add_right
          rw [Nat.div_add_mod m 2] at this
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
      have qpos : 0 < q := by
        have nq : q ≠ 0 := by
          intro H; simp [H] at hq0; contradiction
        exact Nat.pos_of_ne_zero nq
      have hlist : nat_to_bin_list m = (ih q (by
        -- prove q < m:
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
          have ff := foldl_append_one (ih q (by
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
-- </vc-helpers>

-- <vc-spec>
def Mul (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
-- Implement multiplication by converting binary strings to Nat, multiplying, and converting back.

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
  apply nat_to_bin_list_spec
-- </vc-proof>

end BignumLean