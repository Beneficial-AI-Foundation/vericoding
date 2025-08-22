//IMPL swap3
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
{
  var temp := a[i];
  a[i] := a[j];
  a[j] := a[h];
  a[h] := temp;
}

//IMPL testSwap3
method testSwap3(a: array<int>, h: int, i: int, j:int )
  modifies a
  requires 0 <= h < a.Length
  requires 0 <= i < a.Length
  requires 0 <= j < a.Length
  requires i != j && j != h && h != i;
{
  swap3(a, h, i, j);
}