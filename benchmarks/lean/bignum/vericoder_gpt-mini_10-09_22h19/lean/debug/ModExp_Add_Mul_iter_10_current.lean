namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def Add (s1 s2 : String) : String :=
  sorry

axiom Add_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Add s1 s2) ∧ Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2

def Mul (s1 s2 : String) : String :=
  sorry

axiom Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2

-- <vc-helpers>
-- LLM HELPER
open Nat

-- Build binary digits list by accumulating bits (MSB-first).
def nat_to_bin_list_aux : Nat -> List Char -> List Char
  | 0, acc => if acc = [] then ['0'] else acc
  | n+1, acc =>
    let r := (n+1) % 2
    nat_to_bin_list_aux ((n+1) / 2) ((if r = 1 then '1' else '0') :: acc)

termination_by nat_to_bin_list_aux (n acc) => n
decreasing_by
  intros n acc
  cases n
  · simp
  · apply Nat.div_lt_self
    decide

def nat_to_bin_list (n : Nat) : List Char := nat_to_bin_list_aux n []

def nat_to_bin (n : Nat) : String := String.mk (nat_to_bin_list n).toArray

theorem toArray_get?_eq {α : Type} : ∀ (l : List α) (i : Nat), (l.toArray).get? i = l.get? i := by
  intro l
  induction l with
  | nil =>
    intro i
    simp [List.toArray, Array.get?, List.get?]
    cases i <;> simp
  | cons hd tl ih =>
    intro i
    simp [List.toArray]
    cases i
    · simp [Array.get?, List.get?]
    · have : (tl.toArray).get? i = tl.get? i := ih i
      simp [Array.get?, List.get?] at this
      exact this

theorem toArray_foldl_eq_foldl {α β : Type} (l : List β) (f : α -> β -> α) (init : α) :
  (l.toArray).foldl f init = l.foldl f init := by
  induction l with
  | nil =>
    simp [List.toArray, Array.foldl, List.foldl]
  | cons hd tl ih =>
    simp [List.toArray]
    -- use definition of Array.foldl on Array.push
    -- Array.push here corresponds to building array from list; simp reduces the foldl accordingly
    have : (Array.push (tl.toArray) hd).foldl f init = (tl.toArray).foldl f (f init hd) := by
      simp [Array.foldl]
    calc
      (hd :: tl).toArray.foldl f init = (Array.push (tl.toArray) hd).foldl f init := rfl
      _ = (tl.toArray).foldl f (f init hd) := by rw [this]
      _ = tl.foldl f (f init hd) := by rw [ih]
      _ = (hd :: tl).foldl f init := by simp [List.foldl]

theorem List.get?_append {α : Type} : ∀ (l1 l2 : List α) (i : Nat),
  (l1 ++ l2).get? i = (if i < l1.length then l1.get? i else l2.get? (i - l1.length)) := by
  intros l1 l2
  induction l1 with
  | nil =>
    intros i
    simp [List.get?]
  | cons hd tl ih =>
    intros i
    simp [List.get?]
    cases i
    · simp
    · -- i = i+1, use IH on tl
      have : (tl ++ l2).get? i = (if i < tl.length then tl.get? i else l2.get? (i - tl.length)) := ih l2 i
      rw [this]
      by_cases h : i + 1 < (tl.length + 1)
      · have : i < tl.length := by
          apply Nat.lt_of_succ_lt_succ
          exact h
        simp [this]
      · -- i+1 >= tl.length+1
        have : ¬ (i < tl.length) := by
          intro hc
          have := Nat.succ_lt_succ hc
          exact (not_lt_of_ge (Nat.le_of_lt_succ h)) this
        simp [this]
        congr
        have : i - tl.length = (i + 1) - (tl.length + 1) := by
          apply Nat.sub_eq_sub_iff_eq_add
          · apply Nat.le_of_lt_succ h
          · simp
        exact this

theorem nat_to_bin_list_correct : ∀ n, (nat_to_bin_list n).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = n := by
  intro n
  apply Nat.strong_induction_on n
  intro n IH
  cases n
  case zero =>
    simp [nat_to_bin_list, nat_to_bin_list_aux]
  case succ n' =>
    cases n'
    case zero =>
      -- n = 1
      simp [nat_to_bin_list, nat_to_bin_list_aux]
    case succ n'' =>
      let q := n / 2
      let r := n % 2
      have defn : nat_to_bin_list n = nat_to_bin_list q ++ [if r = 1 then '1' else '0'] := by
        simp [nat_to_bin_list, nat_to_bin_list_aux]
      rw [defn]
      calc
        (nat_to_bin_list n).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
          = ([if r = 1 then '1' else '0'] : List Char).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0))
              ((nat_to_bin_list q).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) := by
            apply List.foldl_append
        _ = (if r = 1 then 1 else 0) + 2 * ((nat_to_bin_list q).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) := by
            simp
        _ = (if r = 1 then 1 else 0) + 2 * q := by
            have q_lt_n : q < n := by
              apply Nat.div_lt_self
              decide
            have IHq := IH q q_lt_n
            rw [IHq]
        _ = n := by
            have dv := Nat.div_mod_eq n 2
            simp [dv]; ring

theorem nat_to_bin_list_chars : ∀ n i c, (nat_to_bin_list n).get? i = some c -> (c = '0' ∨ c = '1') := by
  intro n
  apply Nat.strong_induction_on n
  intro n IH
  cases n
  case zero =>
    intros i c h
    simp [nat_to_bin_list, nat_to_bin_list_aux] at h
    cases i
    · simp [List.get?] at h; injection h with hc; subst hc; left; rfl
    · simp [List.get?] at h; contradiction
  case succ n' =>
    cases n'
    case zero =>
      -- n = 1 -> list = ['1']
      intros i c h
      simp [nat_to_bin_list, nat_to_bin_list_aux] at h
      cases i
      · simp [List.get?] at h; injection h with hc; subst hc; right; rfl
      · simp [List.get?] at h; contradiction
    case succ n'' =>
      let q := n / 2
      let r := n % 2
      have defn : nat_to_bin_list n = nat_to_bin_list q ++ [if r = 1 then '1' else '0'] := by
        simp [nat_to_bin_list, nat_to_bin_list_aux]
      intros i c h
      rw [defn] at h
      have eq := List.get?_append (nat_to_bin_list q) ([if r = 1 then '1' else '0']) i
      rw [eq] at h
      by_cases hi : i < (nat_to_bin_list q).length
      · simp [hi] at h
        have q_lt_n : q < n := by
          apply Nat.div_lt_self
          decide
        have IHq := IH q q_lt_n
        apply IHq i c h
      · simp [hi] at h
        by_cases heq : i = (nat_to_bin_list q).length
        · simp [heq] at h
          injection h with hc
          subst hc
          by_cases hr : r = 1
          · simp [hr]; right; rfl
          · simp [hr]; left; rfl
        · simp [heq] at h
          contradiction
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
def ModExp (sx sy sz : String) : String :=
  nat_to_bin (Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz)
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
  let n := Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz
  dsimp [ModExp]
  split
  · -- ValidBitString
    intros i c h
    simp [nat_to_bin] at h
    have := toArray_get?_eq (nat_to_bin_list n) i
    rw [this] at h
    apply nat_to_bin_list_chars n i c h
  · -- Numeric equality
    dsimp [nat_to_bin]
    have : (nat_to_bin_list n).toArray.foldl (fun (acc : Nat) (ch : Char) => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
           (nat_to_bin_list n).foldl (fun (acc : Nat) (ch : Char) => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
      apply toArray_foldl_eq_foldl
    simp [Str2Int]
    rw [this]
    exact nat_to_bin_list_correct n
-- </vc-theorem>
-- <vc-proof>
-- Proofs are provided inline in the helper and theorem sections above.
-- No additional proof content required here.
-- </vc-proof>

end BignumLean