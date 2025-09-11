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
def nat_to_bin_list : Nat -> List Char :=
  WellFounded.fix (measure_wf id) (fun n IH =>
    match n with
    | 0 => ['0']
    | 1 => ['1']
    | _ =>
      let q := n / 2
      let r := n % 2
      let q_val := IH q (by
        -- q = n / 2 < n for n >= 2
        have h : 2 > 0 := by decide
        apply Nat.div_lt_self _ h)
      q_val ++ [if r = 1 then '1' else '0']
    end)

-- Convert a nat to a binary String (MSB-first) by turning the char list into an Array and making a String.
def nat_to_bin (n : Nat) : String :=
  String.mk ((nat_to_bin_list n).toArray)

-- Lemma: converting list to array preserves indexing (get?).
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
    · -- i = i+1
      have : (tl.toArray).get? i = tl.get? i := ih i
      simp [Array.get?, List.get?] at this
      exact this

-- Lemma: folding over the array obtained from a list equals folding over the list.
theorem toArray_foldl_eq_foldl {α β : Type} (l : List β) (f : α -> β -> α) (init : α) :
  (l.toArray).foldl f init = l.foldl f init := by
  induction l with
  | nil =>
    simp [List.toArray, Array.foldl, List.foldl]
  | cons hd tl ih =>
    simp [List.toArray]
    -- Array constructed is (tl.toArray).push hd
    -- foldl over (tl.toArray).push hd equals folding over tl.toArray then f with hd
    have : (Array.push (tl.toArray) hd).foldl f init = (tl.toArray).foldl f (f init hd) := by
      -- unfold Array.foldl for push: it's definitionally equal to folding over tl.toArray with updated accumulator
      simp [Array.foldl]
    calc
      (hd :: tl).toArray.foldl f init = (Array.push (tl.toArray) hd).foldl f init := by rfl
      _ = (tl.toArray).foldl f (f init hd) := by rw [this]
      _ = tl.foldl f (f init hd) := by rw [ih]
      _ = (hd :: tl).foldl f init := by simp [List.foldl]

-- Helper: get? on list append behaves as follows.
theorem List.get?_append {α : Type} : ∀ (l1 l2 : List α) (i : Nat),
  (l1 ++ l2).get? i = (if i < l1.length then l1.get? i else l2.get? (i - l1.length)) := by
  intros l1 l2
  induction l1 with
  | nil =>
    intros i
    simp [List.get?]
    by_cases h : i < 0
    · contradiction
    simp [h]
  | cons hd tl ih =>
    intros i
    simp [List.get?]
    cases i
    · simp
    · -- i = i+1, use IH on tl
      have : (tl ++ l2).get? i = (if i < tl.length then tl.get? i else l2.get? (i - tl.length)) := ih tl l2 i
      rw [this]
      by_cases h : i + 1 < (tl.length + 1)
      · have : i < tl.length := by
          apply Nat.lt_of_succ_lt_succ
          exact h
        simp [this]
      · have : ¬ (i < tl.length) := by
          intro hc
          have := Nat.succ_lt_succ hc
          exact (not_lt_of_ge (Nat.le_of_lt_succ h)) this
        simp [this]
        congr
        apply Nat.sub_eq_iff_eq_add_of_le
        · apply Nat.le_of_lt_succ h
        · simp

-- The numeric correctness: fold over nat_to_bin_list reconstructs the original number.
theorem nat_to_bin_list_correct : ∀ n, (nat_to_bin_list n).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = n := by
  intro n
  apply WellFounded.induction (measure_wf id) n
  intro n IH
  cases n
  case zero =>
    simp [nat_to_bin_list]
  case succ n' =>
    cases n'
    case zero =>
      -- n = 1
      simp [nat_to_bin_list]
    case succ n'' =>
      -- n >= 2
      let q := n / 2
      let r := n % 2
      have defn : nat_to_bin_list n = nat_to_bin_list q ++ [if r = 1 then '1' else '0'] := by
        -- Unfold the WellFounded.fix-based definition
        simp [nat_to_bin_list]
      rw [defn]
      -- foldl over appended list
      calc
        (nat_to_bin_list n).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
          = ([if r = 1 then '1' else '0'] : List Char).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) ((nat_to_bin_list q).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) := by
            apply List.foldl_append
        _ = (if r = 1 then 1 else 0) + 2 * ((nat_to_bin_list q).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) := by
            simp
        _ = (if r = 1 then 1 else 0) + 2 * q := by
            -- use IH on q: q < n
            have q_lt_n : q < n := by
              apply Nat.div_lt_self
              decide
            have IHq := IH q q_lt_n
            rw [IHq]
        _ = n := by
            -- n = 2*q + r by div_mod_eq
            have dv := Nat.div_mod_eq n 2
            simp [dv]; ring

-- Lemma: every character produced is either '0' or '1'
theorem nat_to_bin_list_chars : ∀ n i c, (nat_to_bin_list n).get? i = some c -> (c = '0' ∨ c = '1') := by
  intro n
  apply WellFounded.induction (measure_wf id) n
  intro n IH
  cases n
  case zero =>
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
      let q := n / 2
      let r := n % 2
      have defn : nat_to_bin_list n = nat_to_bin_list q ++ [if r = 1 then '1' else '0'] := by
        simp [nat_to_bin_list]
      intros i c h
      rw [defn] at h
      -- use the general get?_append lemma to reason about index
      have eq := List.get?_append (nat_to_bin_list q) ([if r = 1 then '1' else '0']) i
      rw [eq] at h
      by_cases hi : i < (nat_to_bin_list q).length
      · -- prefix: use IH for q
        simp [hi] at h
        have q_lt_n : q < n := by
          apply Nat.div_lt_self
          decide
        have IHq := IH q q_lt_n
        apply IHq i c h
      · -- either last element or out of bounds
        simp [hi] at h
        by_cases heq : i = (nat_to_bin_list q).length
        · -- last element
          simp [heq] at h
          injection h with hc
          subst hc
          by_cases hr : r = 1
          · simp [hr]; right; rfl
          · simp [hr]; left; rfl
        · -- out of bounds (i > length) gives no some value
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
  -- define numeric value
  let n := Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz
  -- unfold ModExp and replace with nat_to_bin n
  dsimp [ModExp]
  change nat_to_bin n = nat_to_bin (Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz) at *
  -- now prove both parts about nat_to_bin n
  split
  · -- ValidBitString: show every character of the constructed string is '0' or '1'
    intros i c h
    -- unfold nat_to_bin and relate array indexing to list indexing
    simp [nat_to_bin] at h
    -- use toArray_get?_eq to relate array.get? and list.get?
    have := toArray_get?_eq (nat_to_bin_list n) i
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
-- All required proofs have been provided in the helper and theorem sections above.
-- No additional proof content is required here.
-- </vc-proof>

end BignumLean