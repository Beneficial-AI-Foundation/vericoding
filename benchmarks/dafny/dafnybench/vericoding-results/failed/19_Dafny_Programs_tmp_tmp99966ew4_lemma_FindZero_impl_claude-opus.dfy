

// <vc-helpers>
ghost predicate NoZero(a: array<int>, n: int)
  requires 0 <= n <= a.Length
  reads a
{
  forall i :: 0 <= i < n ==> a[i] != 0
}

lemma NoZeroAfterFullScan(a: array<int>, n: int)
  requires 0 <= n <= a.Length
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
  requires forall i :: 0 <= i < n ==> a[i] != 0
  requires n == a.Length
  ensures forall i :: 0 <= i < a.Length ==> a[i] != 0
{
  // If we've checked all elements and found no zeros, then there are no zeros
  // This follows directly from the precondition
}
// </vc-helpers>

// <vc-spec>
method FindZero(a: array<int>) returns (index: int)
   requires a != null
   requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
   requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
   ensures index < 0  ==> forall i :: 0 <= i < a.Length ==> a[i] != 0
   ensures 0 <= index ==> index < a.Length && a[index] == 0
// </vc-spec>
// <vc-code>
{
  index := 0;
  while index < a.Length
    invariant 0 <= index <= a.Length
    invariant forall i :: 0 <= i < index ==> a[i] != 0
  {
    if a[index] == 0 {
      return;
    }
    index := index + 1;
  }
  
  // At this point, index == a.Length and we've verified all elements are non-zero
  assert forall i :: 0 <= i < a.Length ==> a[i] != 0;
  index := -1;
}
// </vc-code>

