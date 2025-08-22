// ATOM BN_11
predicate ValidBitString(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

// ATOM BN_31
opaque function Pow2(n: nat): nat
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

// ATOM BN_40
function Str2Int(s: string): nat
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
} 

// IMPL BN_5
lemma Bound(s : string)
requires ValidBitString(s)
ensures Pow2(|s|) > Str2Int(s)
{
  if |s| == 0 {
    reveal Pow2();
  } else {
    var prefix := s[0..|s|-1];
    var lastBit := s[|s|-1];
    
    assert ValidBitString(prefix);
    Bound(prefix);
    
    reveal Pow2();
    
    if lastBit == '1' {
      assert Str2Int(s) == 2 * Str2Int(prefix) + 1;
      assert Pow2(|s|) == 2 * Pow2(|prefix|);
      assert Pow2(|prefix|) > Str2Int(prefix);
      assert 2 * Pow2(|prefix|) > 2 * Str2Int(prefix) + 1;
    } else {
      assert Str2Int(s) == 2 * Str2Int(prefix);
      assert Pow2(|s|) == 2 * Pow2(|prefix|);
      assert Pow2(|prefix|) > Str2Int(prefix);
      assert 2 * Pow2(|prefix|) > 2 * Str2Int(prefix);
    }
  }
}