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
  assume false;
}
// </vc-code>

/*
*/