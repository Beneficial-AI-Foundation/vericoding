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
function Zeros_func(n: nat): (s: string)
  ensures |s| == n
  ensures AllZero(s)
{
  if n == 0 then "" else Zeros_func(n - 1) + "0"
}

lemma AllZero_implies_properties(s: string)
  requires AllZero(s)
  ensures ValidBitString(s) && Str2Int(s) == 0
  decreases |s|
{
  forall i | 0 <= i < |s|
    ensures s[i] == '0' || s[i] == '1'
  {
    assert s[i] == '0';
  }

  if |s| > 0 {
    var prefix := s[0..|s|-1];
    assert AllZero(prefix);
    AllZero_implies_properties(prefix);
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
  s := Zeros_func(n);
  AllZero_implies_properties(s);
}
// </vc-code>
