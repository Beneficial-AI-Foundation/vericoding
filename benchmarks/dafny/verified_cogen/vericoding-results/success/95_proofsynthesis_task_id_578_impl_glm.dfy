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
  /* code modified by LLM (iteration 2): Added loop invariant to help Dafny verify postcondition */
  var n := s1.Length;
  res := new int[n * 3];
  for i := 0 to n
    invariant forall j :: 0 <= j < i ==> (res[3 * j] == s1[j] && res[3 * j + 1] == s2[j] && res[3 * j + 2] == s3[j])
  {
    res[3 * i] := s1[i];
    res[3 * i + 1] := s2[i];
    res[3 * i + 2] := s3[i];
  }
}
// </vc-code>
