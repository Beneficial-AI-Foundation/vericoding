//ATOM

method max(a: array<int>, b: array<int>, i: int, j: int)
 returns (m: int)
 requires 0 <= i < a.Length
 requires 0 <= j < b.Length
 ensures a[i] > b[j] ==> m == a[i]
 ensures a[i] <= b[j] ==> m == b[j]
{
  m := 0;
  assume a[i] > b[j] ==> m == a[i];
  assume a[i] <= b[j] ==> m == b[j];
  return m;
}


// SPEC

method testMax(a:array<int>, b:array<int>, i: int, j: int)
 requires 0 <= i < a.Length
 requires 0 <= j < b.Length
{
}