// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method LessEqual(a: array<int>, b: array<int>) returns (result: array<bool>)
    requires a.Length == b.Length
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> result[i] == (a[i] <= b[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): added loop invariant to ensure postcondition */
  var n := a.Length;
  result := new bool[n];
  for i := 0 to n
    invariant forall j :: 0 <= j < i ==> result[j] == (a[j] <= b[j])
  {
    result[i] := a[i] <= b[i];
  }
}
// </vc-code>
