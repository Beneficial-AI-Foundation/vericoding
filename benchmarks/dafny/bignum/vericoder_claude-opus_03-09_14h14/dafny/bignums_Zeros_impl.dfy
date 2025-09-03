predicate AllZero(s: string)
{
  |s| == 0 || forall i | 0 <= i < |s| :: s[i] == '0'
}
ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
predicate ValidBitString(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

// <vc-helpers>
lemma AllZeroImpliesStr2IntZero(s: string)
  requires ValidBitString(s)
  requires AllZero(s)
  ensures Str2Int(s) == 0
  decreases |s|
{
  if |s| == 0 {
    // Base case: empty string
    assert Str2Int(s) == 0;
  } else {
    // Inductive case
    var s' := s[0..|s|-1];
    
    // s' is also all zeros
    assert forall i | 0 <= i < |s'| :: s'[i] == s[i] == '0';
    assert AllZero(s');
    
    // s' is a valid bit string
    assert ValidBitString(s');
    
    // Apply induction hypothesis
    AllZeroImpliesStr2IntZero(s');
    assert Str2Int(s') == 0;
    
    // The last character is '0'
    assert s[|s|-1] == '0';
    
    // Therefore Str2Int(s) == 0
    assert Str2Int(s) == 2 * Str2Int(s') + 0 == 0;
  }
}
// </vc-helpers>

// <vc-spec>
method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
// </vc-spec>
// <vc-code>
{
  s := "";
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant |s| == i
    invariant ValidBitString(s)
    invariant AllZero(s)
  {
    s := s + "0";
    i := i + 1;
  }
  
  AllZeroImpliesStr2IntZero(s);
}
// </vc-code>

