// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IterCopy(s: array<int>) returns (result: array<int>)
    ensures
        s.Length == result.Length &&
        forall i :: 0 <= i < s.Length ==> s[i] == result[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): removed trailing semi-colon in loop invariant */
  result := new int[s.Length];
  for i := 0 to s.Length
    invariant forall j :: 0 <= j < i ==> result[j] == s[j]
  {
    result[i] := s[i];
  }
}
// </vc-code>
