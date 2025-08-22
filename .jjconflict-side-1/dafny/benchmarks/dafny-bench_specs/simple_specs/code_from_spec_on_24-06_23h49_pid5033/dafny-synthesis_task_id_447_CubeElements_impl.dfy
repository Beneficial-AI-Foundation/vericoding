//IMPL CubeElements
method CubeElements(a: array<int>) returns (cubed: array<int>)
  ensures cubed.Length == a.Length
  ensures forall i :: 0 <= i < a.Length ==> cubed[i] == a[i] * a[i] * a[i]
{
  cubed := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant cubed.Length == a.Length
    invariant forall j :: 0 <= j < i ==> cubed[j] == a[j] * a[j] * a[j]
  {
    cubed[i] := a[i] * a[i] * a[i];
    i := i + 1;
  }
}