//IMPL
method Sign(a: array<int>) returns (res: array<int>)
ensures res.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> 
  (a[i] > 0 ==> res[i] == 1) &&
  (a[i] == 0 ==> res[i] == 0) &&
  (a[i] < 0 ==> res[i] == -1)
{
  res := new int[a.Length];
  
  var j := 0;
  while j < a.Length
    invariant 0 <= j <= a.Length
    invariant forall k :: 0 <= k < j ==> 
      (a[k] > 0 ==> res[k] == 1) &&
      (a[k] == 0 ==> res[k] == 0) &&
      (a[k] < 0 ==> res[k] == -1)
  {
    if a[j] > 0 {
      res[j] := 1;
    } else if a[j] == 0 {
      res[j] := 0;
    } else {
      res[j] := -1;
    }
    j := j + 1;
  }
}