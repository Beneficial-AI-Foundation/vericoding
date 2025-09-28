// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method TwoWaySort(a: array<bool>)
    requires a.Length <= 100_000
    ensures multiset(a[..]) == old(multiset(a[..]))
    ensures forall i, j :: 0 <= i < j < a.Length ==> !a[i] || a[j]
    modifies a
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 3): added loop invariants to ensure postconditions are verified, handled array bounds with conditions */
var left := 0;
var right := a.Length - 1;
while left <= right && left < a.Length && right >= 0
  invariant 0 <= left <= right + 1 <= a.Length
  invariant forall i :: 0 <= i < left ==> !a[i]
  invariant forall i :: right < i < a.Length ==> a[i]
  invariant multiset(a[..]) == old(multiset(a[..]))
{
  while left <= right && !a[left]
    invariant 0 <= left <= right + 1 <= a.Length
    invariant forall i :: 0 <= i < left ==> !a[i]
    invariant forall i :: right < i < a.Length ==> a[i]
    invariant multiset(a[..]) == old(multiset(a[..]))
    { left := left + 1; }
  while left <= right && a[right]
    invariant 0 <= left <= right + 1 <= a.Length
    invariant forall i :: 0 <= i < left ==> !a[i]
    invariant forall i :: right < i < a.Length ==> a[i]
    invariant multiset(a[..]) == old(multiset(a[..]))
    { right := right - 1; }
  if left <= right
  {
    a[left], a[right] := a[right], a[left];
    left := left + 1;
    right := right - 1;
  }
}
}
// </vc-code>
