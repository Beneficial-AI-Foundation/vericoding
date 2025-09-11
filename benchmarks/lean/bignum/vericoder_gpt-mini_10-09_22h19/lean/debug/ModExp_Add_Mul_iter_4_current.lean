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
def nat_to_bin_list (n : Nat) : List Char :=
  match n with
  | 0 => ['0']
  | 1 => ['1']
  | _ =>
    let q := n / 2
    let r := n % 2
    (nat_to_bin_list q) ++ [if r = 1 then '1' else '0']

termination_by _ => n
decreasing_by
  simp_all
  -- for the branch n >= 2 we need q < n
  show (n / 2) < n
  apply Nat.div_lt_self
  decide

-- Convert a nat to a binary String (MSB-first) by turning the char list into an Array and making a String.
def nat_to_bin (n : Nat) : String :=
  String.mk ((nat_to_bin_list n).toArray)

-- Lemma: converting list to array preserves indexing (get?).
theorem toArray_get?_eq {α : Type} : ∀ (l : List α) (i : Nat), (l.toArray).get? i = l.get? i := by
  intro l
  induction l with
  | nil =>
    intro i
    simp [List.toArray]
    -- empty array, nothing to get
    cases i <;> simp [Array.get?, List.get?]
  | cons hd tl ih =>
    intro i
    simp [List.toArray]
    -- the array built from cons is tl.toArray.push hd
    cases i
    · -- i = 0
      simp [Array.get?, List.get?]
    · -- i = i+1
      have : (tl.toArray).get? i = tl.get? i := ih i
      simp [Array.get?, List.get?] at this
      exact this

-- Lemma: folding over the array obtained from a list equals folding over the list.
theorem toArray_foldl_eq_foldl {α β : Type} (l : List β) (f : α -> β -> α) (init : α) :
  (l.toArray).foldl f init = l.foldl f init := by
  induction l with
  | nil =>
    simp [List.toArray, Array.foldl]
  | cons hd tl ih =>
    simp [List.toArray]
    -- Array constructed is (tl.toArray).push hd
    -- Array.foldl (tl.toArray.push hd) f init = f ((tl.toArray).foldl f init) hd
    simp [Array.foldl]
    rw [ih]
    simp [List.foldl]

-- The numeric correctness: fold over nat_to_bin_list reconstructs the original number.
theorem nat_to_bin_list_correct : ∀ n, (nat_to_bin_list n).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = n := by
  -- use well-founded induction on the length of the produced list (this gives a strong-like induction)
  apply well_founded_induction (measure_wf fun k => (nat_to_bin_list k).length)
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
      let m := succ (succ n'')
      have hm : n = m := rfl
      -- compute q and r
      let q := n / 2
      let r := n % 2
      have defn : nat_to_bin_list n = nat_to_bin_list q ++ [if r = 1 then '1' else '0'] := by
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
            -- use IH on q: its produced list length is smaller by one
            have lenq : (nat_to_bin_list q).length < (nat_to_bin_list n).length := by
              -- nat_to_bin_list n = nat_to_bin_list q ++ [_], so length increases by 1
              simp [defn]
              apply Nat.lt_succ_self
            have IHq := IH q lenq
            rw [IHq]
        _ = n := by
            -- n = 2*q + r by div_mod_eq
            have dv := Nat.div_mod_eq n 2
            simp [dv]

-- Lemma: every character produced is either '0' or '1'
theorem nat_to_bin_list_chars : ∀ n i c, (nat_to_bin_list n).get? i = some c -> (c = '0' ∨ c = '1') := by
  apply well_founded_induction (measure_wf fun k => (nat_to_bin_list k).length)
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
      let m := succ (succ n'')
      have hm : n = m := rfl
      let q := n / 2
      let r := n % 2
      have defn : nat_to_bin_list n = nat_to_bin_list q ++ [if r = 1 then '1' else '0'] := by
        simp [nat_to_bin_list]
      intros i c h
      rw [defn] at h
      -- consider whether i indexes into the prefix or the last element
      by_cases hi : i < (nat_to_bin_list q).length
      · -- prefix: use IH for q
        have hget := List.get?_append_of_lt _ _ hi
        rw [hget] at h
        -- q's produced list length is smaller than n's produced list length
        have lenq : (nat_to_bin_list q).length < (nat_to_bin_list n).length := by
          simp [defn]
          apply Nat.lt_succ_self
        have : (nat_to_bin_list q).get? i = some c := h
        have IHq := IH q lenq
        apply IHq i c this
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
-- Proofs for ModExp_spec and supporting lemmas are provided above in the theorem and helper lemmas.
-- </vc-proof>

end BignumLean