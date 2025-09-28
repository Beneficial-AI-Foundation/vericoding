// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method subtract(a: array<int>, b: array<int>) returns (result: array<int>)
    requires a.Length == b.Length
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> result[i] == a[i] - b[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): added loop invariant to prove postcondition */
  result := new int[a.Length];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> result[j] == a[j] - b[j]
  {
    result[i] := a[i] - b[i];
  }
}
// </vc-code>
