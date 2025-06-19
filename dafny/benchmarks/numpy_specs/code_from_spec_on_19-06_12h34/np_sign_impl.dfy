//IMPL
method Sign(a: array<int>) returns (res: array<int>)
ensures res.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> 
  (a[i] > 0 ==> res[i] == 1) &&
  (a[i] == 0 ==> res[i] == 0) &&
  (a[i] < 0 ==> res[i] == -1)
{
  res := new int[a.Length];
  for i := 0 to a.Length
    invariant forall j :: 0 <= j < i ==> 
      (a[j] > 0 ==> res[j] == 1) &&
      (a[j] == 0 ==> res[j] == 0) &&
      (a[j] < 0 ==> res[j] == -1)
  {
    if a[i] > 0 {
      res[i] := 1;
    } else if a[i] == 0 {
      res[i] := 0;
    } else {
      res[i] := -1;
    }
  }
}