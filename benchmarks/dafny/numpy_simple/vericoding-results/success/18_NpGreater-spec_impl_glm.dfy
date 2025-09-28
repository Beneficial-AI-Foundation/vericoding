// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Greater(a: array<int>, b: array<int>) returns (result: array<bool>)
    requires a.Length == b.Length
    ensures 
        result.Length == a.Length &&
        forall i :: 0 <= i < a.Length ==> result[i] == (a[i] > b[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): added loop invariant to prove postcondition */
  result := new bool[a.Length];
  for i := 0 to a.Length
    invariant forall j :: 0 <= j < i ==> result[j] == (a[j] > b[j])
  {
    result[i] := a[i] > b[i];
  }
}
// </vc-code>
