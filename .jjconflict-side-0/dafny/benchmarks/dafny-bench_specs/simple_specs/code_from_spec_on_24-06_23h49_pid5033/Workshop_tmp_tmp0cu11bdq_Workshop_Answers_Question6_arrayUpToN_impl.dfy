//IMPL
method arrayUpToN(n: int) returns (a: array<int>)
  requires n >= 0
  ensures a.Length == n
  ensures forall j :: 0 < j < n ==> a[j] >= 0
  ensures forall j, k : int :: 0 <= j <= k < n ==> a[j] <= a[k]
{
  a := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] == 0
  {
    a[i] := 0;
    i := i + 1;
  }
}