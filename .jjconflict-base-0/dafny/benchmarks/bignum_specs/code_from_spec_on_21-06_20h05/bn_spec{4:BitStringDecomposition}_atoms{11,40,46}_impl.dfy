//ATOM BN_11
predicate ValidBitString(s: string) 
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

//ATOM BN_46 
function Exp_int(x: nat, y:nat): nat 
{
  if y == 0 then 1 else x * Exp_int(x, y-1)
}

//ATOM BN_40
function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

//IMPL BN_4
lemma BitStringDecomposition(s: string, i: int) 
requires ValidBitString(s) && i < |s|
ensures i >= 0 ==> Str2Int(s[0..i+1]) == Str2Int(s[0..i]) * 2 + (if s[i] == '1' then 1 else 0)
{
  if i >= 0 {
    var prefix := s[0..i+1];
    assert ValidBitString(prefix);
    assert |prefix| == i + 1;
    assert prefix[|prefix|-1] == s[i];
    
    if i == 0 {
      assert s[0..1] == [s[0]];
      assert s[0..0] == [];
      assert Str2Int(s[0..0]) == 0;
    } else {
      assert prefix[0..|prefix|-1] == s[0..i];
    }
  }
}