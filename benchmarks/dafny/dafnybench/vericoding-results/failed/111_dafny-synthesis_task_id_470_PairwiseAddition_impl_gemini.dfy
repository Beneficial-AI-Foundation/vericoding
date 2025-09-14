// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method PairwiseAddition(a: array<int>) returns (result: array<int>)
    requires a != null
    requires a.Length % 2 == 0
    ensures result != null
    ensures result.Length == a.Length / 2
    ensures forall i :: 0 <= i < result.Length ==> result[i] == a[2*i] + a[2*i + 1]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Switched from a forall statement to a while loop to address a compilation warning issue. */
  result := new int[a.Length / 2];
  var i := 0;
  while i < result.Length
    invariant 0 <= i <= result.Length
    invariant forall j :: 0 <= j < i ==> result[j] == a[2*j] + a[2*j + 1]
  {
    result[i] := a[2*i] + a[2*i+1];
    i := i + 1;
  }
}
// </vc-code>
