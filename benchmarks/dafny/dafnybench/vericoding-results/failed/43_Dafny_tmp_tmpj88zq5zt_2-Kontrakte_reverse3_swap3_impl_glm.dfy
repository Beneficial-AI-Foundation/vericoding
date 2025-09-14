

// <vc-helpers>

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
{
  var temp := a[h];
  a[h] := a[i];
  a[i] := a[j];
  a[j] := temp;
}
// </vc-code>

