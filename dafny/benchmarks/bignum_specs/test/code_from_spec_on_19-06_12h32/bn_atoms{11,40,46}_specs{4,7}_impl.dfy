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

//IMPL
lemma BitStringDecomposition(s: string, i: int) 
requires ValidBitString(s) && i < |s|
ensures i >= 0 ==> Str2Int(s[0..i+1]) == Str2Int(s[0..i]) * 2 + (if s[i] == '1' then 1 else 0)
{
  if i >= 0 {
    /* code modified by LLM (iteration 1): Added precondition checks and proper proof structure */
    assert i < |s|;
    assert i + 1 <= |s|;
    
    var prefix := s[0..i+1];
    var shorter := s[0..i];
    
    /* code modified by LLM (iteration 1): Added validity assertions for substrings */
    assert ValidBitString(prefix);
    assert ValidBitString(shorter);
    
    if i == 0 {
      /* code modified by LLM (iteration 1): Explicit proof for base case */
      assert shorter == "";
      assert Str2Int(shorter) == 0;
      assert prefix == s[0..1];
      assert |prefix| == 1;
      assert Str2Int(prefix) == 2 * Str2Int(prefix[0..0]) + (if prefix[0] == '1' then 1 else 0);
      assert prefix[0..0] == "";
      assert Str2Int(prefix[0..0]) == 0;
      assert Str2Int(prefix) == (if prefix[0] == '1' then 1 else 0);
      assert prefix[0] == s[0];
    } else {
      /* code modified by LLM (iteration 1): Recursive case proof using Str2Int definition */
      assert |prefix| > 0;
      assert prefix == s[0..i+1];
      assert prefix[0..|prefix|-1] == s[0..i];
      assert prefix[|prefix|-1] == s[i];
      
      // Apply the definition of Str2Int to prefix
      assert Str2Int(prefix) == 2 * Str2Int(prefix[0..|prefix|-1]) + (if prefix[|prefix|-1] == '1' then 1 else 0);
      assert Str2Int(prefix) == 2 * Str2Int(shorter) + (if s[i] == '1' then 1 else 0);
    }
  }
}

//IMPL
method Compare(s1: string, s2: string) returns (res: int) 
requires ValidBitString(s1) && ValidBitString(s2)
ensures Str2Int(s1) < Str2Int(s2) ==> res == -1
ensures Str2Int(s1) == Str2Int(s2) ==> res == 0
ensures Str2Int(s1) > Str2Int(s2) ==> res == 1
{
  /* code modified by LLM (iteration 1): Simplified implementation using direct comparison */
  var val1 := Str2Int(s1);
  var val2 := Str2Int(s2);
  
  if val1 < val2 {
    res := -1;
  } else if val1 == val2 {
    res := 0;
  } else {
    /* code modified by LLM (iteration 1): Added assertion to help verification */
    assert val1 > val2;
    res := 1;
  }
}