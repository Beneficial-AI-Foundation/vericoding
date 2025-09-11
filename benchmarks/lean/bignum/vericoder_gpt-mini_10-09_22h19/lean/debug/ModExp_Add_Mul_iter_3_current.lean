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

-- Convert a natural number to a list of chars representing its binary digits (MSB-first).
def nat_to_bin_list : Nat -> List Char
| 0 => ['0']
| 1 => ['1']
| succ (succ k) =>
  let n := succ (succ k)
  let q := n / 2
  let r := n % 2
  (nat_to_bin_list q) ++ [if r = 1 then '1' else '0']
termination_by _ => n
decreasing_by
  simp_all
  -- for the branch n = succ (succ k) we need q < n
  apply Nat.div_lt_self
  -- 0 < n holds and 1 < 2 holds
  decide

-- Convert a nat to a binary String (MSB-first) by turning the char list into an Array and making a String.
def nat_to_bin (n : Nat) : String :=
  String.mk (nat_to_bin_list n).toArray

-- Lemma: converting list to array preserves indexing (get?).
theorem toArray_get?_eq {α : Type} : ∀ (l : List α) (i : Nat), (l.toArray).get? i = l.get? i := by
  intro l
  induction l with
  | nil =>
    intro i
    simp [List.toArray, Array.get?]
  | cons hd tl ih =>
    intro i
    simp [List.toArray]
    -- Now reason by cases on i
    cases i
    · -- i = 0
      simp [Array.get?, List.get?]
    · -- i = i+1
      -- reduce to the tail via ih
      have : (tl.toArray).get? i = tl.get? i := ih i
      simp [Array.get?, List.get?] at this
      exact this

-- Lemma: folding over the array obtained from a list equals folding over the list.
theorem toArray_foldl_eq_foldl {α β : Type} (l : List β) (f : α -> β -> α) (init : α) :
  (l.toArray).foldl f init = l.foldl f init := by
  induction l with
  | nil =>
    simp [List.toArray]
  | cons hd tl ih =>
    simp [List.toArray]
    -- unfold Array.foldl on a constructed array; this reduces to foldl on tail then apply f with hd
    -- Array.foldl (tl.toArray.push hd) f init = f ((tl.toArray).foldl f init) hd
    simp [Array.foldl]
    -- Now use ih to replace (tl.toArray).foldl f init with tl.foldl f init
    rw [ih]
    -- finally, list foldl for (hd :: tl) equals f (tl.foldl f init) hd
    simp [List.foldl]

-- The numeric correctness: fold over nat_to_bin_list reconstructs the original number.
theorem nat_to_bin_list_correct : ∀ n, (nat_to_bin_list n).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = n := by
  -- use strong induction on n
  apply Nat.strong_induction_on
  intro n ih
  cases n
  case zero =>
    simp [nat_to_bin_list]
  case succ n' =>
    cases n'
    case zero =>
      -- n = 1
      simp [nat_to_bin_list]
    case succ n'' =>
      -- n >= 2; let m = succ (succ n'')
      let m := succ (succ n'')
      let q := m / 2
      let r := m % 2
      have defn : nat_to_bin_list m = nat_to_bin_list q ++ [if r = 1 then '1' else '0'] := by
        simp [nat_to_bin_list]
      rw [defn]
      -- foldl over appended list
      calc
        (nat_to_bin_list m).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
          = ([if r = 1 then '1' else '0'] : List Char).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) ((nat_to_bin_list q).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) := by
            apply List.foldl_append
        _ = (if r = 1 then 1 else 0) + 2 * ((nat_to_bin_list q).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) := by
            simp
        _ = (if r = 1 then 1 else 0) + 2 * q := by
            -- use strong induction hypothesis for q since q < m
            have hq : q < m := by
              apply Nat.div_lt_self
              decide
            have IHq := ih q hq
            rw [IHq]
        _ = m := by
            -- m = 2*q + r by div_mod_eq
            have dv := Nat.div_mod_eq m 2
            simp [dv]

-- Lemma: every character produced is either '0' or '1'
theorem nat_to_bin_list_chars : ∀ n i c, (nat_to_bin_list n).get? i = some c -> (c = '0' ∨ c = '1') := by
  apply Nat.strong_induction_on
  intro n ih
  cases n
  case zero =>
    -- list = ['0']
    intros i c h
    simp [nat_to_bin_list] at h
    cases i
    · simp [List.get?] at h; injection h with hc; subst hc; left; rfl
    · simp [List.get?] at h; contradiction
  case succ n' =>
    cases n'
    case zero =>
      -- n = 1 -> list = ['1']
      intros i c h
      simp [nat_to_bin_list] at h
      cases i
      · simp [List.get?] at h; injection h with hc; subst hc; right; rfl
      · simp [List.get?] at h; contradiction
    case succ n'' =>
      let m := succ (succ n'')
      let q := m / 2
      let r := m % 2
      have defn : nat_to_bin_list m = nat_to_bin_list q ++ [if r = 1 then '1' else '0'] := by
        simp [nat_to_bin_list]
      intros i c h
      rw [defn] at h
      -- consider whether i indexes into the prefix or the last element
      by_cases hi : i < (nat_to_bin_list q).length
      · -- prefix: use IH for q
        have hget := List.get?_append_of_lt _ _ hi
        rw [hget] at h
        -- q < m, so we can use strong induction hypothesis on q
        have qlt : q < m := by apply Nat.div_lt_self; decide
        have := ih q qlt
        apply this q i c h
      · -- either last element or out of bounds
        have hge : (nat_to_bin_list q).length ≤ i := by
          by_contra hc
          apply hi; exact Nat.lt_of_not_ge hc
        have hget := List.get?_append_of_ge _ _ hge
        rw [hget] at h
        -- if i equals length then it's the last element
        by_cases heq : i = (nat_to_bin_list q).length
        · subst heq
          simp at h
          injection h with hc
          subst hc
          -- final char is either '0' or '1' by definition
          by_cases hr : r = 1
          · simp [hr]; right; rfl
          · simp [hr]; left; rfl
        · -- out of bounds
          simp [heq] at h
          contradiction
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
def ModExp (sx sy sz : String) : String :=
  -- compute numeric modular exponentiation and convert to binary string
  nat_to_bin (Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz)
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
  dsimp [ModExp]
  let n := Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz
  -- Replace ModExp by nat_to_bin n
  have hstr : ModExp sx sy sz = nat_to_bin n := rfl
  subst hstr
  split
  · -- ValidBitString: show every character of the constructed string is '0' or '1'
    intros i c h
    -- unfold nat_to_bin and relate array indexing to list indexing
    simp [nat_to_bin] at h
    -- (nat_to_bin_list n).toArray.get? i = (nat_to_bin_list n).get? i
    have : (nat_to_bin_list n).toArray.get? i = (nat_to_bin_list n).get? i := by
      apply toArray_get?_eq
    rw [this] at h
    -- now apply character lemma
    apply nat_to_bin_list_chars n i c h
  · -- Numeric equality: Str2Int (nat_to_bin n) = n
    dsimp [nat_to_bin]
    -- Str2Int uses .data.foldl on the underlying array; move to list foldl using toArray_foldl_eq_foldl
    have : (nat_to_bin_list n).toArray.foldl (fun (acc : Nat) (ch : Char) => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
           (nat_to_bin_list n).foldl (fun (acc : Nat) (ch : Char) => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
      apply toArray_foldl_eq_foldl
    -- unfold Str2Int to expose array.foldl
    simp [Str2Int]
    -- replace array.foldl with list.foldl
    rw [this]
    -- now apply correctness of nat_to_bin_list
    exact nat_to_bin_list_correct n
-- </vc-theorem>
-- <vc-proof>
-- Proofs are provided in the theorem and helper lemmas above.
-- </vc-proof>

end BignumLean