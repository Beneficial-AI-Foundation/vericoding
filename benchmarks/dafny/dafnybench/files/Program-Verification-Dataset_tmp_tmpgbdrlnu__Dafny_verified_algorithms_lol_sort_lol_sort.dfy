// <vc-preamble>
predicate valid_permut(a: seq<int>, b: seq<int>)
  requires |a| == |b|
{
  multiset(a) == multiset(b)
}

method swap(a: array<int>, i: int, j: int)
  requires 0 <= i < a.Length && 0 <= j < a.Length
  modifies a
  ensures a[..] == old(a[..]) [i := old(a[j])] [j := old(a[i])]
  ensures valid_permut(a[..], old(a[..]))
{
  assume{:axiom} false;
}

predicate sorted(a: seq<int>)
{
  forall i, j | 0 <= i <= j < |a| :: a[i] <= a[j]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method lol_sort(a: array<int>)
  modifies a
  ensures valid_permut(a[..], old(a[..]))
  ensures sorted(a[..])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
