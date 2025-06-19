// ATOMS
// BN_11
predicate ValidBitString(s: string) 
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

//BN_46 
function Exp_int(x: nat, y:nat): nat 
{
  if y == 0 then 1 else x * Exp_int(x, y-1)
}

// BN_40
function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

// SPECIFICATION 
// BN_4
lemma BitStringDecomposition(s: string, i: int) 
requires ValidBitString(s) && i < |s|
ensures i >= 0 ==> Str2Int(s[0..i+1]) == Str2Int(s[0..i]) * 2 + (if s[i] == '1' then 1 else 0)
{}

// SPECIFICATION
//BN_7
method Compare(s1: string, s2: string) returns (res: int) 
requires ValidBitString(s1) && ValidBitString(s2)
ensures Str2Int(s1) < Str2Int(s2) ==> res == -1
ensures Str2Int(s1) == Str2Int(s2) ==> res == 0
ensures Str2Int(s1) > Str2Int(s2) ==> res == 1
{}