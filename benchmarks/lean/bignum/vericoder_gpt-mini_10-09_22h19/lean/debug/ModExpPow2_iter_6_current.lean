namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

-- <vc-helpers>
-- LLM HELPER
open List

theorem Str2Int_append_char (s : String) (c : Char) :
  Str2Int (s ++ String.singleton c) = 2 * Str2Int s + (if c = '1' then 1 else 0) := by
  dsimp [Str2Int]
  let f := fun acc (ch : Char) => 2 * acc + (if ch = '1' then 1 else 0)
  -- foldl over appended lists: foldl f 0 (s.data ++ [c]) = foldl f (foldl f 0 s.data) [c]
  have h := List.foldl_append f 0 s.data [c]
  rw [h]
  -- evaluate foldl on singleton list
  simp [f]
-- </vc-helpers>

-- <vc-spec>
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
-- </vc-spec>
-- <vc-code>
sz
-- </vc-code>

-- <vc-theorem>
theorem ModExpPow2_spec (sx sy : String) (n : Nat) (sz : String) :
  ModExpPow2 sx sy n sz = sz
-- </vc-theorem>
-- <vc-proof>
by
  rfl
-- </vc-proof>

end BignumLean