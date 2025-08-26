method Cubes(a: array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == i*i*i
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] == j*j*j
  {
    a[i] := i*i*i;
    i := i + 1;
  }
}
// </vc-code>