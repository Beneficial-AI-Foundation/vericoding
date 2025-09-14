/*
*/

// <vc-helpers>
// No helpers needed for this fix
// </vc-helpers>

// <vc-spec>
method Getmini(a:array<int>) returns(mini:nat) 
requires a.Length > 0
ensures 0 <= mini < a.Length // mini is an index of a
ensures forall x :: 0 <= x < a.Length ==> a[mini] <= a[x] // a[mini] is the minimum value
ensures forall x :: 0 <= x < mini ==> a[mini] < a[x] // a[mini] is the first min
// </vc-spec>
// <vc-code>
{
  var minIndex: nat := 0;
  var minValue: int := a[0];
  for i: nat := 1 to a.Length
    invariant 0 <= minIndex < a.Length
    invariant a[minIndex] == minValue
    invariant forall x :: 0 <= x < i ==> a[minIndex] <= a[x]
    invariant minIndex < i
    invariant forall x :: 0 <= x < minIndex ==> a[minIndex] < a[x]
  {
    if a[i] < minValue {
      minIndex := i;
      minValue := a[i];
    }
  }
  return minIndex;
}
// </vc-code>

