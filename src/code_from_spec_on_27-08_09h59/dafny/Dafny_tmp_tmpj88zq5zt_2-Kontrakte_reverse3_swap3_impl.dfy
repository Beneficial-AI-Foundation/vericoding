// <vc-helpers>
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
  var temp_h := a[h];
  var temp_i := a[i];
  var temp_j := a[j];
  
  a[h] := temp_i;
  a[i] := temp_j;
  a[j] := temp_h;
}
// </vc-code>
