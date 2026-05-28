// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): No changes, helper seems correct */
lemma AllZeroProperties(s: string)
  requires AllZero(s)
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  decreases |s|
{
  if |s| > 0 {
    var prefix := s[0..|s|-1];
    assert AllZero(prefix);
    AllZeroProperties(prefix);
    assert ValidBitString(s);
    assert s[|s|-1] == '0';
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
  /* code modified by LLM (iteration 3): Added i <= n invariant to prove final length */
  s := "";
  var i: nat := 0;
  while i < n
    invariant |s| == i
    invariant AllZero(s)
    invariant i <= n
  {
    s := s + "0";
    i := i + 1;
  }
  AllZeroProperties(s);
}
// </vc-code>
