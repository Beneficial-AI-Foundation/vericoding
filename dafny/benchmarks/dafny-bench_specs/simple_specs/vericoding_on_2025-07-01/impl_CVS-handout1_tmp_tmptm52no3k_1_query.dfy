//ATOM

//(a)

function sum(a: array<int>, i: int, j: int): int
  reads a
  requires 0 <= i <= j <= a.Length
{
  if (i == j) then 0
  else a[i] + sum(a, i+1, j)
}


// SPEC



//(b)

method query(a: array<int>, i: int, j: int) returns (res:int)
  requires 0 <= i <= j <= a.Length
  ensures res == sum(a, i, j)
{
}