//IMPL Swap method

method Swap (a : array?<int>, i : int, j : int)
  requires a != null && 0 <= i < a.Length && 0 <= j < a.Length
  modifies a
{
  var temp := a[i];
  a[i] := a[j];
  a[j] := temp;
}