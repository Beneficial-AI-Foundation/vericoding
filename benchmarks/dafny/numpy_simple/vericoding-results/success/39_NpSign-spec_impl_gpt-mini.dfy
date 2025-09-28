// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SignVal(x: int): int {
  if x > 0 then 1 else if x < 0 then -1 else 0
}
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
  var n := a.Length;
  result := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> (
      (a[j] > 0 ==> result[j] == 1) &&
      (a[j] == 0 ==> result[j] == 0) &&
      (a[j] < 0 ==> result[j] == -1)
    )
    decreases n - i
  {
    if a[i] > 0 {
      result[i] := 1;
    } else if a[i] < 0 {
      result[i] := -1;
    } else {
      result[i] := 0;
    }
    i := i + 1;
  }
}
// </vc-code>
