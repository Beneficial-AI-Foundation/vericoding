// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method interleave(s1: array<int>, s2: array<int>, s3: array<int>) returns (res: array<int>)
    requires s1.Length == s2.Length && s2.Length == s3.Length
    requires 0 <= (s1.Length * 3)
    ensures res.Length == s1.Length * 3
    ensures forall i :: 0 <= i < s1.Length ==> (res[3 * i] == s1[i] && res[3 * i + 1] == s2[i] && res[3 * i + 2] == s3[i])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var pos := 0;
  res := new int[s1.Length * 3];
  while i < s1.Length
    invariant 0 <= i <= s1.Length
    invariant pos == 3 * i
    invariant forall k :: 0 <= k < i ==> (
      res[3 * k] == s1[k] &&
      res[3 * k + 1] == s2[k] &&
      res[3 * k + 2] == s3[k])
  {
    res[pos] := s1[i];
    pos := pos + 1;
    res[pos] := s2[i];
    pos := pos + 1;
    res[pos] := s3[i];
    pos := pos + 1;
    i := i + 1;
  }
}
// </vc-code>
