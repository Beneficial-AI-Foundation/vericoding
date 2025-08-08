//SPEC
method Sign(a: array<int>) returns (res: array<int>)
ensures res.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> 
  (a[i] > 0 ==> res[i] == 1) &&
  (a[i] == 0 ==> res[i] == 0) &&
  (a[i] < 0 ==> res[i] == -1)
  {}