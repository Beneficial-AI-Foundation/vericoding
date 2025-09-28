// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method IsSorted(lst: array<int>) returns (result: bool)
    requires lst.Length >= 1
    ensures result ==> forall i, j :: 0 <= i && i < j && j < lst.Length ==> lst[i] <= lst[j]
    ensures !result ==> exists i, j :: 0 <= i && i < j && j < lst.Length && lst[i] > lst[j]
// </vc-spec>
// <vc-code>
{
  var n := lst.Length;
  if n == 1 {
    result := true;
    return;
  }
  if !(lst[0] <= lst[1]) {
    result := false;
    return;
  }
  var i := 1;
  while i < n - 1
    invariant 1 <= i <= n - 1
    invariant forall p, q :: 0 <= p && p < q && q <= i ==> lst[p] <= lst[q]
  {
    if !(lst[i] <= lst[i+1]) {
      result := false;
      return;
    }
    i := i + 1;
  }
  result := true;
}
// </vc-code>
