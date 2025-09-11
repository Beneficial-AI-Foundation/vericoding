namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
-- Helpers to convert Nat to binary String and basic lemmas about them.

open Std

def nat_bits_aux : Nat -> List Char
  | 0 => []
  | m+1 => nat_bits_aux ((m+1) / 2) ++ [if (m+1) % 2 = 1 then '1' else '0']

def nat_to_bin_list (n : Nat) : List Char :=
  match n with
  | 0 => ['0']
  | _ => nat_bits_aux n

def nat_to_bin_str (n : Nat) : String :=
  String.mk (nat_to_bin_list n)

theorem nat_bits_aux_chars (m : Nat) : ∀ {ch}, ch ∈ nat_bits_aux m → ch = '0' ∨ ch = '1' := by
  induction m using Nat.strong_induction_on with
  | ih m =>
    cases m
    case zero =>
      simp [nat_bits_aux]; intros ch h; cases h
    case succ m' =>
      have split : nat_bits_aux (m' + 1) = nat_bits_aux ((m' + 1) / 2) ++ [if (m' + 1) % 2 = 1 then '1' else '0'] := rfl
      intros ch h
      simp [split] at h
      rcases h with
      | inl hin =>
        -- apply IH to the smaller index (division by 2 is strictly smaller)
        have hlt : ( (m' + 1) / 2) < (m' + 1) := by
          have : 0 < 2 := by norm_num
          -- use the standard division strictness lemma
          exact Nat.div_lt_self (by decide) (by norm_num)
        exact ih ((m' + 1) / 2) hlt ch hin
      | inr heq =>
        -- ch equals the last bit; decide whether it is '0' or '1'
        simp at heq
        let bit := if (m' + 1) % 2 = 1 then '1' else '0'
        have : ch = bit := heq
        by_cases hbit : (m' + 1) % 2 = 1
        · simp [bit, hbit]; left; rfl
        · simp [bit, hbit]; right; rfl

theorem nat_to_bin_list_chars (n : Nat) : ∀ {ch}, ch ∈ nat_to_bin_list n → ch = '0' ∨ ch = '1' := by
  cases n
  case zero =>
    simp [nat_to_bin_list]; intros ch h
    simp at h
    rcases h with rfl | rfl
    · left; rfl
    · cases h -- impossible
  case succ n' =>
    -- for positive n, nat_to_bin_list uses nat_bits_aux
    simp [nat_to_bin_list]
    apply nat_bits_aux_chars

theorem Str2Int_nat_bits_aux_aux {l : List Char} :
  (fun ls => ls.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) l = l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := rfl

theorem Str2Int_nat_to_bin_str (n : Nat) : Str2Int (nat_to_bin_str n) = n := by
  induction n using Nat.strong_induction_on with
  | ih n =>
    cases n
    case zero =>
      simp [nat_to_bin_str, nat_to_bin_list, Str2Int]
      -- nat_to_bin_list 0 = ['0'], foldl over "0" gives 0
      simp [List.foldl]; rfl
    case succ n' =>
      have aux_def : nat_to_bin_list (Nat.succ n') = nat_bits_aux (Nat.succ n') := by simp [nat_to_bin_list]
      simp [nat_to_bin_str, aux_def]
      let m := Nat.succ n'
      have split : nat_bits_aux m = nat_bits_aux (m / 2) ++ [if m % 2 = 1 then '1' else '0'] := rfl
      simp [split]
      set u := nat_bits_aux (m / 2) with hu
      set b := (if m % 2 = 1 then '1' else '0') with hb
      have fold_concat : (u ++ [b]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
                         2 * (u.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) +
                         (if b = '1' then 1 else 0) := by
        calc
          (u ++ [b]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
            = [b].foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) (u.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) := by
              rw [List.foldl_append]
            _ = 2 * (u.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) + (if b = '1' then 1 else 0) := by
              simp [List.foldl]
      simp [fold_concat]
      -- Apply IH to u: u corresponds to m/2 which is strictly smaller than m
      have ih_apply : (u.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) = (m /
-- </vc-helpers>

-- <vc-spec>
def DivMod (s1 s2 : String) : (String × String) :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
-- Helpers to convert Nat to binary String and basic lemmas about them.

open Std

def nat_bits_aux : Nat -> List Char
  | 0 => []
  | m+1 => nat_bits_aux ((m+1) / 2) ++ [if (m+1) % 2 = 1 then '1' else '0']

def nat_to_bin_list (n : Nat) : List Char :=
  match n with
  | 0 => ['0']
  | _ => nat_bits_aux n

def nat_to_bin_str (n : Nat) : String :=
  String.mk (nat_to_bin_list n)

theorem nat_bits_aux_chars (m : Nat) : ∀ {ch}, ch ∈ nat_bits_aux m → ch = '0' ∨ ch = '1' := by
  induction m using Nat.strong_induction_on with
  | ih m =>
    cases m
    case zero =>
      simp [nat_bits_aux]; intros ch h; cases h
    case succ m' =>
      have split : nat_bits_aux (m' + 1) = nat_bits_aux ((m' + 1) / 2) ++ [if (m' + 1) % 2 = 1 then '1' else '0'] := rfl
      intros ch h
      simp [split] at h
      rcases h with
      | inl hin =>
        -- apply IH to the smaller index (division by 2 is strictly smaller)
        have hlt : ( (m' + 1) / 2) < (m' + 1) := by
          have : 0 < 2 := by norm_num
          -- use the standard division strictness lemma
          exact Nat.div_lt_self (by decide) (by norm_num)
        exact ih ((m' + 1) / 2) hlt ch hin
      | inr heq =>
        -- ch equals the last bit; decide whether it is '0' or '1'
        simp at heq
        let bit := if (m' + 1) % 2 = 1 then '1' else '0'
        have : ch = bit := heq
        by_cases hbit : (m' + 1) % 2 = 1
        · simp [bit, hbit]; left; rfl
        · simp [bit, hbit]; right; rfl

theorem nat_to_bin_list_chars (n : Nat) : ∀ {ch}, ch ∈ nat_to_bin_list n → ch = '0' ∨ ch = '1' := by
  cases n
  case zero =>
    simp [nat_to_bin_list]; intros ch h
    simp at h
    rcases h with rfl | rfl
    · left; rfl
    · cases h -- impossible
  case succ n' =>
    -- for positive n, nat_to_bin_list uses nat_bits_aux
    simp [nat_to_bin_list]
    apply nat_bits_aux_chars

theorem Str2Int_nat_bits_aux_aux {l : List Char} :
  (fun ls => ls.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) l = l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := rfl

theorem Str2Int_nat_to_bin_str (n : Nat) : Str2Int (nat_to_bin_str n) = n := by
  induction n using Nat.strong_induction_on with
  | ih n =>
    cases n
    case zero =>
      simp [nat_to_bin_str, nat_to_bin_list, Str2Int]
      -- nat_to_bin_list 0 = ['0'], foldl over "0" gives 0
      simp [List.foldl]; rfl
    case succ n' =>
      have aux_def : nat_to_bin_list (Nat.succ n') = nat_bits_aux (Nat.succ n') := by simp [nat_to_bin_list]
      simp [nat_to_bin_str, aux_def]
      let m := Nat.succ n'
      have split : nat_bits_aux m = nat_bits_aux (m / 2) ++ [if m % 2 = 1 then '1' else '0'] := rfl
      simp [split]
      set u := nat_bits_aux (m / 2) with hu
      set b := (if m % 2 = 1 then '1' else '0') with hb
      have fold_concat : (u ++ [b]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
                         2 * (u.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) +
                         (if b = '1' then 1 else 0) := by
        calc
          (u ++ [b]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
            = [b].foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) (u.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) := by
              rw [List.foldl_append]
            _ = 2 * (u.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) + (if b = '1' then 1 else 0) := by
              simp [List.foldl]
      simp [fold_concat]
      -- Apply IH to u: u corresponds to m/2 which is strictly smaller than m
      have ih_apply : (u.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) = (m /
-- </vc-code>

end BignumLean