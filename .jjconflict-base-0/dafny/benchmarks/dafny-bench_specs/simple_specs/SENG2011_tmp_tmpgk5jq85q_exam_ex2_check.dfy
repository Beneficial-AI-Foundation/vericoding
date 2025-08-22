//ATOM
method Getmini(a:array<int>) returns(mini:nat) 
requires a.Length > 0
ensures 0 <= mini < a.Length // mini is an index of a
ensures forall x :: 0 <= x < a.Length ==> a[mini] <= a[x] // a[mini] is the minimum value
ensures forall x :: 0 <= x < mini ==> a[mini] < a[x] // a[mini] is the first min
{
  mini := 0;
  assume 0 <= mini < a.Length // mini is an index of a;
  assume forall x :: 0 <= x < a.Length ==> a[mini] <= a[x] // a[mini] is the minimum value;
  assume forall x :: 0 <= x < mini ==> a[mini] < a[x] // a[mini] is the first min;
  return mini;
}

/*


// SPEC
method check() {
}
*/
