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
  /* code modified by LLM (iteration 3): Used while loop to properly handle empty arrays and added decreases for termination */
  result := new int[s.Length];
  var i := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant forall j :: 0 <= j < i ==> result[j] == s[j]
    decreases s.Length - i
  {
    result[i] := s[i];
    i := i + 1;
  }
}
// </vc-code>
