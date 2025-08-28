// <vc-helpers>
lemma NonNegativeArray(a: array<int>, i: int)
  requires 0 <= i < a.Length
  requires forall j :: 0 <= j < a.Length ==> 0 <= a[j]
  ensures 0 <= a[i]
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method FindZero(a: array<int>) returns (index: int)
   requires a != null
   requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
   requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
   ensures index < 0  ==> forall i :: 0 <= i < a.Length ==> a[i] != 0
   ensures 0 <= index ==> index < a.Length && a[index] == 0
// </vc-spec>
// </vc-spec>

// <vc-code>
method FindZeroImpl(a: array<int>) returns (index: int)
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
  ensures index < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != 0
  ensures 0 <= index ==> index < a.Length && a[index] == 0
{
  index := -1;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant index < 0 ==> forall k :: 0 <= k < i ==> a[k] != 0
    invariant 0 <= index ==> index < a.Length && a[index] == 0
  {
    if a[i] == 0 {
      index := i;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
