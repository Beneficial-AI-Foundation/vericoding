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
| 0     => ['0']
| 1     => ['1']
| n     => let q := n / 2; let r := n % 2; (nat_to_bin_list q) ++ [if r = 1 then '1' else '0']
termination_by _ => Nat
decreasing_by
  -- show q < n when n >= 2
  simp_all
  apply Nat.div_lt_self
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
    simp [List.toArray]
  | cons hd tl ih =>
    intro i
    -- List.toArray (hd :: tl) = (tl.toArray).push hd ? actually implementation order differs,
    -- but simp will normalize accesses; use cases on i
    simp [List.toArray]
    -- unfold Array.get? on a constructed array; reduce by cases on i
    -- For robustness use general body: compare lengths
    -- We'll reason by cases on i
    cases i
    · -- i = 0
      simp [Array.get?, List.get?]
    · -- i = i+1
      -- relate get? on pushed array to get? on tail
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
    -- unfolding Array.foldl on a built array reduces to foldl on tail and then apply f with hd
    -- reduce goal to ih
    simp [Array.foldl]
    -- Now use ih to finish (the specifics of Array.foldl unfolding are handled by simp)
    apply ih

-- The numeric correctness: fold over nat_to_bin_list reconstructs the original number.
theorem nat_to_bin_list_correct : ∀ n, (nat_to_bin_list n).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = n := by
  intro n
  induction n with
  | zero =>
    simp [nat_to_bin_list]
  | succ n' =>
    cases n' with
    | zero =>
      -- n = 1
      simp [nat_to_bin_list]
    | succ n'' =>
      -- n >= 2
      let nfull := n.succ
      let q := nfull / 2
      let r := nfull % 2
      have defn : nat_to_bin_list nfull = nat_to_bin_list q ++ [if r = 1 then '1' else '0'] := by
        simp [nat_to_bin_list]
      rw [defn]
      calc
        (nat_to_bin_list nfull).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
            = ([if r = 1 then '1' else '0'] : List Char).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) ((nat_to_bin_list q).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) := by
              apply List.foldl_append
        _ = (if r = 1 then 1 else 0) + 2 * ((nat_to_bin_list q).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) := by
              simp
        _ = (if r = 1 then 1 else 0) + 2 * q := by
              have IH := nat_to_bin_list_correct q
              rw [IH]
        _ = nfull := by
              -- nfull = 2*q + r
              have dv := Nat.div_mod_eq nfull 2
              -- r = nfull % 2 and q = nfull / 2 by definition
              simp at dv
              exact dv

-- Lemma: every character produced is either '0' or '1' (by index get?)
theorem nat_to_bin_list_chars : ∀ n i c, (nat_to_bin_list n).get? i = some c -> (c = '0' ∨ c = '1') := by
  intro n
  induction n with
  | zero =>
    intros i c h; simp [nat_to_bin_list] at h; cases i <;> simp at h; contradiction <|> simp [*]; finish
  | succ n' =>
    cases n' with
    | zero =>
      intros i c h; simp [nat_to_bin_list] at h; cases i <;> simp at h; contradiction <|> simp [*]; finish
    | succ n'' =>
      let nfull := n.succ
      let q := nfull / 2
      let r := nfull % 2
      have defn : nat_to_bin_list nfull = nat_to_bin_list q ++ [if r = 1 then '1' else '0'] := by simp [nat_to_bin_list]
      intros i c h
      rw [defn] at h
      by_cases hb : i < (nat_to_bin_list q).length
      · -- in prefix
        have hget := List.get?_append_of_lt _ _ hb
        rw [hget] at h
        apply n_ih
        exact h
      · -- either last element or out of bounds
        have hge : (nat_to_bin_list q).length ≤ i := by
          apply Nat.not_lt.1
          intro con; apply hb; exact con
        have hget := List.get?_append_of_ge _ _ hge
        rw [hget] at h
        -- h is either some of last or none
        by_cases heq : i = (nat_to_bin_list q).length
        · subst heq; simp at h; injection h with hch; clear h; subst hch; simp [if_pos]; finish
        · -- out of bounds leads to contradiction
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
  -- The statement is that nat_to_bin produces a valid bitstring and that its numeric value matches the given nat.
  dsimp [ModExp]
  let n := Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz
  -- Split goals
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
    simp [Str2Int]
    -- now apply correctness of nat_to_bin_list
    rw [this]
    exact nat_to_bin_list_correct n
-- </vc-theorem>
-- <vc-proof>
-- Proofs are provided in the theorem and helper lemmas above.
-- </vc-proof>

end BignumLean