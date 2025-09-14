

// <vc-helpers>
method swap3(a: array<int>, h: int, i: int, j: int)
  modifies a
  requires 0 <= h < a.Length
  requires 0 <= i < a.Length
  requires 0 <= j < a.Length
  requires i != j && j != h && h != i
  ensures a[h] == old(a[i])
  ensures a[j] == old(a[h])
  ensures a[i] == old(a[j])
  ensures forall k: int :: 0 <= k < a.Length && k != h && k != i && k != j ==> a[k] == old(a[k])
{

}
// </vc-helpers>

// <vc-spec>
method swap3(a: array<int>, h: int, i: int, j: int)
  modifies a
  requires 0 <= h < a.Length
  requires 0 <= i < a.Length
  requires 0 <= j < a.Length
  requires i != j && j != h && h != i;
  ensures a[h] == old(a[i]);
  ensures a[j] == old(a[h]);
  ensures a[i] == old(a[j]);
  ensures forall k: int :: 0 <= k < a.Length && k != h && k != i && k != j ==> a[k] == old(a[k]);
// </vc-spec>
// <vc-code>
var tempH := a[h];
  var tempI := a[i];
  var tempJ := a[j];
  a[h] := tempI;
  a[j] := tempH;
  a[i] := tempJ;
// </vc-code>

