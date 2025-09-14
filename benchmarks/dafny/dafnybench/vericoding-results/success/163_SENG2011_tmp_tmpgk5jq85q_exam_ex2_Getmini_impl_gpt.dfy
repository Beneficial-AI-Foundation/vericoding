/*
*/

// <vc-helpers>

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
  var i := 1;
  var min := 0;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant 0 <= min < i
    invariant forall x :: 0 <= x < i ==> a[min] <= a[x]
    invariant forall x :: 0 <= x < min ==> a[min] < a[x]
    decreases a.Length - i
  {
    if a[i] < a[min] {
      min := i;
    }
    i := i + 1;
  }
  mini := min;
}
// </vc-code>

