namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def AllZero (s : String) : Prop :=
  ∀ i, s.get? i = some '0'

def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
  sorry

axiom ModExpPow2_spec (sx sy : String) (n : Nat) (sz : String)
  (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pow2 : Str2Int sy = Exp_int 2 n ∨ Str2Int sy = 0)
  (hsy_len : sy.length = n + 1)
  (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExpPow2 sx sy n sz) ∧
  Str2Int (ModExpPow2 sx sy n sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz

def Zeros (n : Nat) : String :=
  sorry

axiom Zeros_spec (n : Nat) :
  let s := Zeros n
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ AllZero s

-- <vc-helpers>
-- LLM HELPER
def nat_to_bin_aux : Nat → List Char → List Char
| 0, []    => ['0']
| 0, acc   => acc
| n+1, acc =>
  let b := if (n+1) % 2 = 1 then '1' else '0'
  nat_to_bin_aux ((n+1) / 2) (b :: acc)

-- LLM HELPER
def Nat2Str (n : Nat) : String :=
  String.mk (nat_to_bin_aux n [])

-- LLM HELPER
theorem foldl_char_cons (c : Char) (l : List Char) :
  (String.mk (c :: l)).data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
  2 * (String.mk l).data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 +
    (if c = '1' then 1 else 0) := by
  -- compute by definition of foldl on cons
  simp [String.mk]
  -- unfold the foldl step for cons
  rfl

-- LLM HELPER
theorem nat_to_bin_aux_correct (n : Nat) (acc : List Char) :
  let l := nat_to_bin_aux n acc
  (String.mk l).data.foldl (fun acc' ch => 2 * acc' + (if ch = '1' then 1 else 0)) 0 =
    (2 ^ acc.length) * n + (String.mk acc).data.foldl (fun acc' ch => 2 * acc' + (if ch = '1' then 1 else 0)) 0 := by
  induction n generalizing acc with
  | zero =>
    dsimp [nat_to_bin_aux]
    by_cases h : acc = []
    · -- acc = []
      have : nat_to_bin_aux 0 ([] : List Char) = ['0'] := rfl
      dsimp [Nat.cast] at *
      dsimp [String.mk]
      simp [h]
      -- compute both sides: left is foldl on ['0'] equals 0, right is 2^0 * 0 + foldl []
      simp [List.foldl]
    · -- acc ≠ []
      -- nat_to_bin_aux 0 acc = acc
      dsimp [nat_to_bin_aux]
      simp [String.mk]
      simp [pow_zero]
      rfl
  | succ k ih =>
    dsimp [nat_to_bin_aux]
    let n' := k + 1
    let b := if n' % 2 = 1 then '1' else '0'
    have hrec := ih (b :: acc)
    -- use the recurrence for foldl on cons
    dsimp at hrec
    -- apply foldl_char_cons to express fold on (b :: acc)
    have fold_cons := foldl_char_cons b acc
    dsimp [String.mk] at fold_cons
    -- From hrec we have:
    -- fold (nat_to_bin_aux k (b::acc)) = 2^(acc.length + 1) * k + fold (b::acc)
    calc
      (String.mk (nat_to_bin_aux (k + 1) acc)).data.foldl (fun acc' ch => 2 * acc' + (if ch = '1' then 1 else 0)) 0 = 
        (String.mk (nat_to_bin_aux k (b :: acc))).data.foldl (fun acc' ch => 2 * acc' + (if ch = '1' then 1 else 0)) 0 := by
          rfl
      _ = (2 ^ (acc.length + 1)) * k + (String.mk (b :: acc)).data.foldl (fun acc' ch => 2 * acc' + (if ch = '1' then 1 else 0)) 0 := by
          exact hrec
      _ = (2 ^ acc.length) * (2 * k) + (2 * (String.mk acc).data.foldl (fun acc' ch => 2 * acc' + (if ch = '1' then 1 else 0)) 0 +
            (if b = '1' then 1 else 0)) := by
          -- expand (String.mk (b :: acc)).foldl using foldl_char_cons
          simp [pow_succ] at *
          rw [fold_cons]
          ring
      _ = (2 ^ acc.length) * (2 * k + (if b = '1' then 1 else 0)) + (String.mk acc).data.foldl (fun acc' ch => 2 * acc' + (if ch = '1' then 1 else 0)) 0 := by
          ring
      _ = (2 ^ acc.length) * (k + 1) + (String.mk acc).data.foldl (fun acc' ch => 2 * acc' + (if ch = '1' then 1 else 0)) 0 := by
          -- show 2*k + bit = k+1 using div/mod identity
          have : 2 * k + (if b = '1' then 1 else 0) = k + 1 := by
            -- compute b based on parity of k+1
            unfold b
            have mod_eq : (k + 1) % 2 = if (k % 2 = 0) then 1 else 0 := by
              -- not needed, use division identity directly
              simp
            -- Use standard division: (k+1) = 2 * (k+1)/2 + (k+1)%2
            have div_mod : (k + 1) = 2 * ((k + 1) / 2) + (k + 1) % 2 := by
              apply Nat.div_add_mod
            -- but (k + 1) / 2 = k / 2 + (if k % 2 = 1 then 1 else 0) ??? Instead use direct arithmetic:
            -- Observe that (k+1) / 2 = k/2 when k even and = k/2 + 1 when k odd; however we can avoid case split:
            -- We can just rely on the general identity above with q = (k+1)/
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
def nat_to_bin_aux : Nat → List Char → List Char
| 0, []    => ['0']
| 0, acc   => acc
| n+1, acc =>
  let b := if (n+1) % 2 = 1 then '1' else '0'
  nat_to_bin_aux ((n+1) / 2) (b :: acc)

-- LLM HELPER
def Nat2Str (n : Nat) : String :=
  String.mk (nat_to_bin_aux n [])

-- LLM HELPER
theorem foldl_char_cons (c : Char) (l : List Char) :
  (String.mk (c :: l)).data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
  2 * (String.mk l).data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 +
    (if c = '1' then 1 else 0) := by
  -- compute by definition of foldl on cons
  simp [String.mk]
  -- unfold the foldl step for cons
  rfl

-- LLM HELPER
theorem nat_to_bin_aux_correct (n : Nat) (acc : List Char) :
  let l := nat_to_bin_aux n acc
  (String.mk l).data.foldl (fun acc' ch => 2 * acc' + (if ch = '1' then 1 else 0)) 0 =
    (2 ^ acc.length) * n + (String.mk acc).data.foldl (fun acc' ch => 2 * acc' + (if ch = '1' then 1 else 0)) 0 := by
  induction n generalizing acc with
  | zero =>
    dsimp [nat_to_bin_aux]
    by_cases h : acc = []
    · -- acc = []
      have : nat_to_bin_aux 0 ([] : List Char) = ['0'] := rfl
      dsimp [Nat.cast] at *
      dsimp [String.mk]
      simp [h]
      -- compute both sides: left is foldl on ['0'] equals 0, right is 2^0 * 0 + foldl []
      simp [List.foldl]
    · -- acc ≠ []
      -- nat_to_bin_aux 0 acc = acc
      dsimp [nat_to_bin_aux]
      simp [String.mk]
      simp [pow_zero]
      rfl
  | succ k ih =>
    dsimp [nat_to_bin_aux]
    let n' := k + 1
    let b := if n' % 2 = 1 then '1' else '0'
    have hrec := ih (b :: acc)
    -- use the recurrence for foldl on cons
    dsimp at hrec
    -- apply foldl_char_cons to express fold on (b :: acc)
    have fold_cons := foldl_char_cons b acc
    dsimp [String.mk] at fold_cons
    -- From hrec we have:
    -- fold (nat_to_bin_aux k (b::acc)) = 2^(acc.length + 1) * k + fold (b::acc)
    calc
      (String.mk (nat_to_bin_aux (k + 1) acc)).data.foldl (fun acc' ch => 2 * acc' + (if ch = '1' then 1 else 0)) 0 = 
        (String.mk (nat_to_bin_aux k (b :: acc))).data.foldl (fun acc' ch => 2 * acc' + (if ch = '1' then 1 else 0)) 0 := by
          rfl
      _ = (2 ^ (acc.length + 1)) * k + (String.mk (b :: acc)).data.foldl (fun acc' ch => 2 * acc' + (if ch = '1' then 1 else 0)) 0 := by
          exact hrec
      _ = (2 ^ acc.length) * (2 * k) + (2 * (String.mk acc).data.foldl (fun acc' ch => 2 * acc' + (if ch = '1' then 1 else 0)) 0 +
            (if b = '1' then 1 else 0)) := by
          -- expand (String.mk (b :: acc)).foldl using foldl_char_cons
          simp [pow_succ] at *
          rw [fold_cons]
          ring
      _ = (2 ^ acc.length) * (2 * k + (if b = '1' then 1 else 0)) + (String.mk acc).data.foldl (fun acc' ch => 2 * acc' + (if ch = '1' then 1 else 0)) 0 := by
          ring
      _ = (2 ^ acc.length) * (k + 1) + (String.mk acc).data.foldl (fun acc' ch => 2 * acc' + (if ch = '1' then 1 else 0)) 0 := by
          -- show 2*k + bit = k+1 using div/mod identity
          have : 2 * k + (if b = '1' then 1 else 0) = k + 1 := by
            -- compute b based on parity of k+1
            unfold b
            have mod_eq : (k + 1) % 2 = if (k % 2 = 0) then 1 else 0 := by
              -- not needed, use division identity directly
              simp
            -- Use standard division: (k+1) = 2 * (k+1)/2 + (k+1)%2
            have div_mod : (k + 1) = 2 * ((k + 1) / 2) + (k + 1) % 2 := by
              apply Nat.div_add_mod
            -- but (k + 1) / 2 = k / 2 + (if k % 2 = 1 then 1 else 0) ??? Instead use direct arithmetic:
            -- Observe that (k+1) / 2 = k/2 when k even and = k/2 + 1 when k odd; however we can avoid case split:
            -- We can just rely on the general identity above with q = (k+1)/
-- </vc-code>

end BignumLean