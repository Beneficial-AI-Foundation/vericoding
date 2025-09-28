// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Sign(a: array<int>) returns (result: array<int>)
    ensures
        result.Length == a.Length
    ensures
        forall i :: 0 <= i < a.Length ==> (
            (a[i] > 0 ==> result[i] == 1) &&
            (a[i] == 0 ==> result[i] == 0) &&
            (a[i] < 0 ==> result[i] == -1)
        )
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Added loop invariant to prove the forall postcondition */
  result := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> (
      (a[k] > 0 ==> result[k] == 1) &&
      (a[k] == 0 ==> result[k] == 0) &&
      (a[k] < 0 ==> result[k] == -1)
    )
  {
    if a[i] > 0 {
      result[i] := 1;
    } else if a[i] == 0 {
      result[i] := 0;
    } else {
      result[i] := -1;
    }
    i := i + 1;
  }
}
// </vc-code>
