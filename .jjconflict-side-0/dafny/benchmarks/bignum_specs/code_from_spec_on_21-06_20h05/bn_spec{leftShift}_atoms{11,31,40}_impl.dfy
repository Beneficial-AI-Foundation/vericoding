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
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

/* code modified by LLM (iteration 1): Added helper lemmas to prove properties needed for verification */
lemma AppendZeroValidBitString(s: string)
  requires ValidBitString(s)
  ensures ValidBitString(s + "0")
{
  var s' := s + "0";
  forall i | 0 <= i < |s'|
    ensures s'[i] == '0' || s'[i] == '1'
  {
    if i < |s| {
      assert s'[i] == s[i];
    } else {
      assert i == |s|;
      assert s'[i] == '0';
    }
  }
}

lemma AppendZeroDoubles(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s + "0") == 2 * Str2Int(s)
{
  var s' := s + "0";
  if |s| == 0 {
    assert s' == "0";
    assert Str2Int(s') == 0;
    assert Str2Int(s) == 0;
  } else {
    assert |s'| > 0;
    assert s'[|s'|-1] == '0';
    assert s'[0..|s'|-1] == s;
    assert Str2Int(s') == 2 * Str2Int(s'[0..|s'|-1]) + 0;
    assert Str2Int(s') == 2 * Str2Int(s);
  }
}

lemma Pow2Multiplicative(i: nat)
  ensures Pow2(i + 1) == 2 * Pow2(i)
{
  reveal Pow2();
}

// IMPL leftShift
method leftShift(s: string, n: nat) returns (res: string)
    requires ValidBitString(s)
    ensures ValidBitString(res)
    ensures Str2Int(res) == Str2Int(s) * Pow2(n)
{
    res := s;
    var i := 0;
    
    /* code modified by LLM (iteration 1): Added initialization proof for base case */
    reveal Pow2();
    assert Pow2(0) == 1;
    
    while i < n
        invariant 0 <= i <= n
        invariant ValidBitString(res)
        invariant Str2Int(res) == Str2Int(s) * Pow2(i)
    {
        /* code modified by LLM (iteration 1): Added proof annotations to establish loop invariant maintenance */
        AppendZeroValidBitString(res);
        AppendZeroDoubles(res);
        Pow2Multiplicative(i);
        
        var old_res := res;
        res := res + "0";
        i := i + 1;
        
        /* code modified by LLM (iteration 1): Added detailed proof steps for invariant maintenance */
        assert Str2Int(res) == 2 * Str2Int(old_res);
        assert Str2Int(old_res) == Str2Int(s) * Pow2(i-1);
        assert Str2Int(res) == 2 * (Str2Int(s) * Pow2(i-1));
        assert Str2Int(res) == Str2Int(s) * (2 * Pow2(i-1));
        assert Pow2(i) == 2 * Pow2(i-1);
        assert Str2Int(res) == Str2Int(s) * Pow2(i);
    }
}