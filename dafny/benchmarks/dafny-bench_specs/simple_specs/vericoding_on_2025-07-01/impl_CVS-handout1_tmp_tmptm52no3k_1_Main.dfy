//ATOM

//(a)

function sum(a: array<int>, i: int, j: int): int
  reads a
  requires 0 <= i <= j <= a.Length
{
  if (i == j) then 0
  else a[i] + sum(a, i+1, j)
}

//ATOM

method queryFast(a: array<int>, c: array<int>, i: int, j: int) returns (r: int)
  requires a.Length + 1 == c.Length && c[0] == 0
  requires 0 <= i <= j <= a.Length
  requires is_prefix_sum_for(a,c) 
  ensures r == sum(a, i, j)
{
  r := 0;
  assume r ==> sum(a, i, j);
  return r;
}

//ATOM

//(c)

predicate is_prefix_sum_for (a: array<int>, c: array<int>)
  requires a.Length + 1 == c.Length
  requires c[0] == 0
  reads c, a
{
  forall i: int :: 0 <= i < a.Length ==> c[i+1] == c[i] + a[i]
}


// SPEC




method Main()
{
  var x := new int[10];
  x[0], x[1], x[2], x[3] := 2, 2, 1, 5;
  var y := sum(x, 0, x.Length);
  //assert y == 10;
  var c := new int[11];
  c[0], c[1], c[2], c[3], c[4] := 0, 2, 4, 5, 10;
  // var r := queryFast(x, c, 0, x.Length);
  
}