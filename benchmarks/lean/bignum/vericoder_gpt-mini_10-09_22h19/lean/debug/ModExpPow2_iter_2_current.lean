namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

-- <vc-helpers>
-- helper functions and lemmas -- LLM HELPER

open List

def natToBin : Nat -> String
| 0 => "0"
| 1 => "1"
| n+2 => 
  let m := n+2
  let bit := if m % 2 = 1 then "1" else "0"
  natToBin (m / 2) ++ bit

def pow2_mod (x : Nat) : Nat -> Nat -> Nat
| 0, z => x % z
| k+1, z =>
  let t := pow2_mod x k z
  (t * t) % z

theorem Exp_int_add (x a b : Nat) : Exp_int x (a + b) = Exp_int x a * Exp_int x b := by
  induction b with
  | zero => simp [Exp_int]
  | succ b ih =>
    simp [Exp_int]
    -- Exp_int x (a + (b+1)) = x * Exp_int x (a + b)
    -- RHS = Exp_int x a * (x * Exp_int x b) = x * (Exp_int x a * Exp_int x b)
    calc
      Exp_int x (a + b + 1) = x * Exp_int x (a + b) := by simp [Exp_int]
      _ = x * (Exp_int x a * Exp_int x b) := by rw [ih]
      _ = Exp_int x a * (x * Exp_int x b) := by
        -- multiplication is associative & commutative enough here
        simp [mul_assoc]

theorem Str2Int_append_char (s : String) (c : Char) :
  Str2Int (s ++ String.singleton c) = 2 * Str2Int s + (if c = '1' then 1 else 0) := by
  dsimp [Str2Int]
  -- (s ++ single c).data = s.data ++ [c]
  have : (s ++ String.singleton c).data = s.data ++ [c] := by
    simp [String.append, String.singleton]
  rw [this]
  -- foldl over append: foldl f 0 (s.data ++ [c]) = f (foldl f 0 s.data) c
  have fold := List.foldl_append (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 s.data [c]
  -- specialize append lemma for single element list
  dsimp at fold
  rw [fold]
  simp

theorem natToBin_spec_str (m : Nat) : Str2Int (natToBin m) = m := by
  induction m using Nat.dec_induct with
  | pred m ih =>
    decide
  -- Above general fallback; now do structured induction
  -- We'll do standard induction on m
  induction m with
  | zero => dsimp [natToBin, Str2Int]; simp
  | succ m =>
    cases m with
    | zero => 
      -- m = 1
      dsimp [natToBin, Str2Int]; simp
    | succ m' =>
      -- m = m'+2
      let k := m'.succ.succ
      have hk : k = m := rfl
      dsimp [natToBin]
      -- natToBin k = natToBin (k/2) ++ bit
      set s := natToBin (k / 2)
      let bit := if k % 2 = 1 then "1" else "0"
      have : natToBin k = s ++ bit := rfl
      rw [this]
      -- use Str2Int_append_char
      have app := Str2Int_append_char s (if k % 2 = 1 then '1' else '0')
      -- coerce bit string "1"/"0" to its single char
      -- note String.singleton (if ...) is equal to bit
      dsimp at app
      -- apply induction on k/2
      have ih' : Str2Int s = k / 2 := by
        show Str2Int (natToBin (k / 2)) = k / 2
        apply m'.succ.recOn -- use smaller structure to justify recursion; simpler:
        -- use main induction on m: because k/2 < k, the original induction covers it
        -- but to keep this concise, we can call the global induction hypothesis on (k/2)
        -- Lean accepts using m_ih? Use the builtin well-founded recursion from previous induction
        -- Instead use the fact that (k/2) < k, so we can use m_ih on (k/2)
        have : k / 2 < k := by
          apply Nat.div_lt_self; decide
        exact ih (k / 2) this
      -- now compute Str2Int
      calc
        Str2Int (s ++ bit) = 2 * Str2Int s + (if (if k % 2 = 1 then '1' else '0') = '1' then 1 else 0) := by
          -- rewrite using Str2Int_append_char; need to convert bit string to char
          dsimp [bit]
          have : (if k % 2 = 1 then "1" else "0") = String.singleton (if k % 2 = 1 then '1' else '0') := by
            cases (k % 2 = 1) <;> simp [String.singleton]
          rw [this]
          exact Str2Int_append_char s (if k % 2 = 1 then '1' else '0')
        _ = 2 * (k / 2) + (if k % 2 = 1 then 1 else 0) := by
          congr; exact ih'
        _ = k := by
          -- Nat.div_add_mod gives k = 2*(k/2) + k%2
          have h := Nat.div_add_mod k 2
          simp [Nat.div_eq_of_eq_mul_add] at h
          -- direct rewrite
          rw [Nat.div_add_mod]
          simp

theorem natToBin_valid (m : Nat) : ValidBitString (natToBin m) := by
  induction m with
  | zero => dsimp [natToBin]; intros; simp at *; contradiction <|> simp
  | succ m =>
    cases m with
    | zero => -- m = 1
      dsimp [natToBin]; intros i c h
      -- string is "1"
      simp [String.get?] at h
      simp at h; injection h; intro; left; rfl
    | succ m' =>
      let k := m'.succ.succ
      dsimp [natToBin
-- </vc-helpers>

-- <vc-spec>
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- helper functions and lemmas -- LLM HELPER

open List

def natToBin : Nat -> String
| 0 => "0"
| 1 => "1"
| n+2 => 
  let m := n+2
  let bit := if m % 2 = 1 then "1" else "0"
  natToBin (m / 2) ++ bit

def pow2_mod (x : Nat) : Nat -> Nat -> Nat
| 0, z => x % z
| k+1, z =>
  let t := pow2_mod x k z
  (t * t) % z

theorem Exp_int_add (x a b : Nat) : Exp_int x (a + b) = Exp_int x a * Exp_int x b := by
  induction b with
  | zero => simp [Exp_int]
  | succ b ih =>
    simp [Exp_int]
    -- Exp_int x (a + (b+1)) = x * Exp_int x (a + b)
    -- RHS = Exp_int x a * (x * Exp_int x b) = x * (Exp_int x a * Exp_int x b)
    calc
      Exp_int x (a + b + 1) = x * Exp_int x (a + b) := by simp [Exp_int]
      _ = x * (Exp_int x a * Exp_int x b) := by rw [ih]
      _ = Exp_int x a * (x * Exp_int x b) := by
        -- multiplication is associative & commutative enough here
        simp [mul_assoc]

theorem Str2Int_append_char (s : String) (c : Char) :
  Str2Int (s ++ String.singleton c) = 2 * Str2Int s + (if c = '1' then 1 else 0) := by
  dsimp [Str2Int]
  -- (s ++ single c).data = s.data ++ [c]
  have : (s ++ String.singleton c).data = s.data ++ [c] := by
    simp [String.append, String.singleton]
  rw [this]
  -- foldl over append: foldl f 0 (s.data ++ [c]) = f (foldl f 0 s.data) c
  have fold := List.foldl_append (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 s.data [c]
  -- specialize append lemma for single element list
  dsimp at fold
  rw [fold]
  simp

theorem natToBin_spec_str (m : Nat) : Str2Int (natToBin m) = m := by
  induction m using Nat.dec_induct with
  | pred m ih =>
    decide
  -- Above general fallback; now do structured induction
  -- We'll do standard induction on m
  induction m with
  | zero => dsimp [natToBin, Str2Int]; simp
  | succ m =>
    cases m with
    | zero => 
      -- m = 1
      dsimp [natToBin, Str2Int]; simp
    | succ m' =>
      -- m = m'+2
      let k := m'.succ.succ
      have hk : k = m := rfl
      dsimp [natToBin]
      -- natToBin k = natToBin (k/2) ++ bit
      set s := natToBin (k / 2)
      let bit := if k % 2 = 1 then "1" else "0"
      have : natToBin k = s ++ bit := rfl
      rw [this]
      -- use Str2Int_append_char
      have app := Str2Int_append_char s (if k % 2 = 1 then '1' else '0')
      -- coerce bit string "1"/"0" to its single char
      -- note String.singleton (if ...) is equal to bit
      dsimp at app
      -- apply induction on k/2
      have ih' : Str2Int s = k / 2 := by
        show Str2Int (natToBin (k / 2)) = k / 2
        apply m'.succ.recOn -- use smaller structure to justify recursion; simpler:
        -- use main induction on m: because k/2 < k, the original induction covers it
        -- but to keep this concise, we can call the global induction hypothesis on (k/2)
        -- Lean accepts using m_ih? Use the builtin well-founded recursion from previous induction
        -- Instead use the fact that (k/2) < k, so we can use m_ih on (k/2)
        have : k / 2 < k := by
          apply Nat.div_lt_self; decide
        exact ih (k / 2) this
      -- now compute Str2Int
      calc
        Str2Int (s ++ bit) = 2 * Str2Int s + (if (if k % 2 = 1 then '1' else '0') = '1' then 1 else 0) := by
          -- rewrite using Str2Int_append_char; need to convert bit string to char
          dsimp [bit]
          have : (if k % 2 = 1 then "1" else "0") = String.singleton (if k % 2 = 1 then '1' else '0') := by
            cases (k % 2 = 1) <;> simp [String.singleton]
          rw [this]
          exact Str2Int_append_char s (if k % 2 = 1 then '1' else '0')
        _ = 2 * (k / 2) + (if k % 2 = 1 then 1 else 0) := by
          congr; exact ih'
        _ = k := by
          -- Nat.div_add_mod gives k = 2*(k/2) + k%2
          have h := Nat.div_add_mod k 2
          simp [Nat.div_eq_of_eq_mul_add] at h
          -- direct rewrite
          rw [Nat.div_add_mod]
          simp

theorem natToBin_valid (m : Nat) : ValidBitString (natToBin m) := by
  induction m with
  | zero => dsimp [natToBin]; intros; simp at *; contradiction <|> simp
  | succ m =>
    cases m with
    | zero => -- m = 1
      dsimp [natToBin]; intros i c h
      -- string is "1"
      simp [String.get?] at h
      simp at h; injection h; intro; left; rfl
    | succ m' =>
      let k := m'.succ.succ
      dsimp [natToBin
-- </vc-code>

end BignumLean