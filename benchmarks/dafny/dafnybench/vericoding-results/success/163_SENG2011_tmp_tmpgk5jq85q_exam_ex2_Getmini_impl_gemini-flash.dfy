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
  var mini_index: nat := 0;
  var i: nat := 1;
  while i < a.Length
    invariant 0 <= mini_index < i <= a.Length
    invariant forall x :: 0 <= x < i ==> a[mini_index] <= a[x]
    invariant forall x :: 0 <= x < mini_index ==> a[mini_index] < a[x]
  {
    if a[i] < a[mini_index] {
      mini_index := i;
    }
    i := i + 1;
  }
  mini := mini_index;
}
// </vc-code>

