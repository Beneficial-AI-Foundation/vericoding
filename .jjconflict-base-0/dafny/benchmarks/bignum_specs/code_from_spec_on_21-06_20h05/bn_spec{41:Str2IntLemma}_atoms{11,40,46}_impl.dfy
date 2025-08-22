// ATOM BN_11
predicate ValidBitString(s: string) 
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

// ATOM BN_40
function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

// ATOM BN_46
function Exp_int(x: nat, y:nat): nat 
{
  if y == 0 then 1 else x * Exp_int(x, y-1)
}

// IMPL BN_41
lemma Str2IntLemma(s: string, i: nat)
requires ValidBitString(s)
requires 0 <= i <= |s|-1
ensures Str2Int(s) == Str2Int(s[..i+1]) * Exp_int(2, |s|-1 - i) + Str2Int(s[i+1..])
{
  /* code modified by LLM (iteration 1): Fixed precondition check and added proper base case handling */
  if |s| == 0 {
    // This case is impossible due to precondition i <= |s|-1 requiring |s| >= 1
    return;
  }
  
  if |s| == 1 {
    // Base case: single character string
    assert i == 0;
    assert s[..i+1] == s;
    assert s[i+1..] == "";
    assert Str2Int(s[i+1..]) == 0;
    assert Exp_int(2, |s|-1 - i) == Exp_int(2, 0) == 1;
    /* code modified by LLM (iteration 1): Added explicit calculation for base case */
    calc {
      Str2Int(s[..i+1]) * Exp_int(2, |s|-1 - i) + Str2Int(s[i+1..]);
      == Str2Int(s) * 1 + 0;
      == Str2Int(s);
    }
  } else {
    // Inductive case for |s| >= 2
    if i == |s| - 1 {
      // Split at the last position
      assert s[..i+1] == s;
      assert s[i+1..] == "";
      assert Str2Int(s[i+1..]) == 0;
      assert Exp_int(2, |s|-1 - i) == Exp_int(2, 0) == 1;
      /* code modified by LLM (iteration 1): Simplified calculation for edge case */
      assert Str2Int(s[..i+1]) * Exp_int(2, |s|-1 - i) + Str2Int(s[i+1..]) == Str2Int(s) * 1 + 0 == Str2Int(s);
    } else {
      // Recursive application: i < |s| - 1
      var s_prefix := s[0..|s|-1];
      /* code modified by LLM (iteration 1): Added proper validity assertion and bounds checking */
      assert ValidBitString(s_prefix);
      assert |s_prefix| == |s| - 1;
      assert 0 <= i <= |s_prefix| - 1;
      
      Str2IntLemma(s_prefix, i);
      
      // Apply the relationship for s_prefix
      assert Str2Int(s_prefix) == Str2Int(s_prefix[..i+1]) * Exp_int(2, |s_prefix|-1 - i) + Str2Int(s_prefix[i+1..]);
      
      /* code modified by LLM (iteration 1): Added explicit slice equality assertions */
      assert s_prefix[..i+1] == s[..i+1];
      assert s_prefix[i+1..] == s[i+1..|s|-1];
      
      // Key insight: Str2Int(s[i+1..]) can be expressed in terms of Str2Int(s[i+1..|s|-1])
      /* code modified by LLM (iteration 1): Added helper assertion for string concatenation property */
      assert s[i+1..] == s[i+1..|s|-1] + [s[|s|-1]];
      assert Str2Int(s[i+1..]) == 2 * Str2Int(s[i+1..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      
      /* code modified by LLM (iteration 1): Added step-by-step calculation with proper justification */
      calc {
        Str2Int(s);
        == { assert Str2Int(s) == 2 * Str2Int(s_prefix) + (if s[|s|-1] == '1' then 1 else 0); }
        2 * Str2Int(s_prefix) + (if s[|s|-1] == '1' then 1 else 0);
        == { /* inductive hypothesis */ }
        2 * (Str2Int(s[..i+1]) * Exp_int(2, |s|-2 - i) + Str2Int(s[i+1..|s|-1])) + (if s[|s|-1] == '1' then 1 else 0);
        == { /* distribute multiplication */ }
        Str2Int(s[..i+1]) * (2 * Exp_int(2, |s|-2 - i)) + 2 * Str2Int(s[i+1..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
        == { assert 2 * Exp_int(2, |s|-2 - i) == Exp_int(2, |s|-1 - i); }
        Str2Int(s[..i+1]) * Exp_int(2, |s|-1 - i) + (2 * Str2Int(s[i+1..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0));
        == { /* property of Str2Int concatenation */ }
        Str2Int(s[..i+1]) * Exp_int(2, |s|-1 - i) + Str2Int(s[i+1..]);
      }
    }
  }
}