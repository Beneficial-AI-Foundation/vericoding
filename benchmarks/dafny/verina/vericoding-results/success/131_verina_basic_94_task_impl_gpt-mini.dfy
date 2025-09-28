// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma NonNegativeLength(s: array<int>)
  ensures s.Length >= 0
{
  assert s.Length >= 0;
}
// </vc-helpers>

// <vc-spec>
method IterCopy(s: array<int>) returns (result: array<int>)
    ensures
        s.Length == result.Length &&
        forall i :: 0 <= i < s.Length ==> s[i] == result[i]
// </vc-spec>
// <vc-code>
{
  result := new int[s.Length];
  var i := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant forall k :: 0 <= k < i ==> result[k] == s[k]
    decreases s.Length - i
  {
    result[i] := s[i];
    i := i + 1;
  }
}
// </vc-code>
