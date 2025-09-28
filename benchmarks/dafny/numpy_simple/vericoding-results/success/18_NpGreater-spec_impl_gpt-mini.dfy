// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function cmp_gt(x: int, y: int): bool {
  x > y
}
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
  var n := a.Length;
  result := new bool[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result.Length == n
    invariant forall j :: 0 <= j < i ==> result[j] == (a[j] > b[j])
  {
    result[i] := cmp_gt(a[i], b[i]);
    i := i + 1;
  }
}

// </vc-code>
