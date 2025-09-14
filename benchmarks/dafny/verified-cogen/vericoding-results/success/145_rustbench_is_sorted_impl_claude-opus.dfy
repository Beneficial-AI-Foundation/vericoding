// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsSorted(lst: array<int>) returns (result: bool)
    requires lst.Length >= 1
    ensures result ==> forall i, j :: 0 <= i && i < j && j < lst.Length ==> lst[i] <= lst[j]
    ensures !result ==> exists i, j :: 0 <= i && i < j && j < lst.Length && lst[i] > lst[j]
// </vc-spec>
// <vc-code>
{
  result := true;
  var i := 0;
  while i < lst.Length - 1
    invariant 0 <= i <= lst.Length - 1
    invariant result ==> forall k, l :: 0 <= k && k < l && l <= i ==> lst[k] <= lst[l]
    invariant !result ==> exists k, l :: 0 <= k && k < l && l < lst.Length && lst[k] > lst[l]
  {
    if lst[i] > lst[i + 1] {
      result := false;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
