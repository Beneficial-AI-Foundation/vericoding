//IMPL max
method max(a: array<int>, b: array<int>, i: int, j: int)
  returns (m: int)
  requires 0 <= i < a.Length
  requires 0 <= j < b.Length
  ensures  a[i] > b[j] ==> m == a[i]
  ensures  a[i] <= b[j] ==> m == b[j]
{
  if a[i] > b[j] {
    m := a[i];
  } else {
    m := b[j];
  }
}

//IMPL testMax
method testMax(a:array<int>, b:array<int>, i: int, j: int)
  requires 0 <= i < a.Length
  requires 0 <= j < b.Length
{
  var result := max(a, b, i, j);
}