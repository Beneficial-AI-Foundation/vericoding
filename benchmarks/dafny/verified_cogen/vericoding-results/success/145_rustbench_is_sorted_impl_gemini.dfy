// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

predicate IsSortedUpTo(a: array<int>, n: int)
  reads a
  requires 0 <= n <= a.Length
{
  forall i, j :: 0 <= i < j < n ==> a[i] <= a[j]
}

lemma SortedExtension(a: array<int>, k: int)
  requires 0 <= k < a.Length - 1
  requires IsSortedUpTo(a, k + 1)
  requires a[k] <= a[k + 1]
  ensures IsSortedUpTo(a, k + 2)
{}

// </vc-helpers>

// <vc-spec>
method IsSorted(lst: array<int>) returns (result: bool)
    requires lst.Length >= 1
    ensures result ==> forall i, j :: 0 <= i && i < j && j < lst.Length ==> lst[i] <= lst[j]
    ensures !result ==> exists i, j :: 0 <= i && i < j && j < lst.Length && lst[i] > lst[j]
// </vc-spec>
// <vc-code>
{
  if lst.Length <= 1 {
    result := true;
    return;
  }

  var k := 0;
  while k < lst.Length - 1
    invariant 0 <= k <= lst.Length - 1
    invariant IsSortedUpTo(lst, k + 1)
  {
    if lst[k] > lst[k+1] {
      result := false;
      return;
    }
    SortedExtension(lst, k);
    k := k + 1;
  }

  result := true;
}
// </vc-code>
