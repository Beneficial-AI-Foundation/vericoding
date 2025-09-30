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
  result := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> (
      (a[j] > 0 ==> result[j] == 1) &&
      (a[j] == 0 ==> result[j] == 0) &&
      (a[j] < 0 ==> result[j] == -1)
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
