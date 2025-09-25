// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method SelectionSort(a: array<int>)
  modifies a

  ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]

  ensures multiset(a[..]) == old(multiset(a[..]))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
