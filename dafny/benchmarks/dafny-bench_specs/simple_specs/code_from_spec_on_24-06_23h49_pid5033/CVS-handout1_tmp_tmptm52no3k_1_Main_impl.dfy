//ATOM

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
  assume r == sum(a, i, j);
  return r;
}

//ATOM

predicate is_prefix_sum_for (a: array<int>, c: array<int>)
  requires a.Length + 1 == c.Length
  requires c[0] == 0
  reads c, a
{
  forall i: int :: 0 <= i < a.Length ==> c[i+1] == c[i] + a[i]
}

//IMPL Main
method Main()
{
  /* code modified by LLM (iteration 1): Fixed array initialization syntax */
  var x := new int[4](i => if i == 0 then 2 else if i == 1 then 2 else if i == 2 then 1 else 5);
  
  /* code modified by LLM (iteration 1): Calculate sum using the sum function */
  var y := sum(x, 0, 4);
  
  /* code modified by LLM (iteration 1): Properly initialize prefix sum array */
  var c := new int[5];
  c[0] := 0;
  c[1] := c[0] + x[0];
  c[2] := c[1] + x[1];
  c[3] := c[2] + x[2];
  c[4] := c[3] + x[3];
  
  /* code modified by LLM (iteration 1): Added demonstration of queryFast method with proper bounds */
  var result := queryFast(x, c, 0, 2);
  print "Sum from index 0 to 2: ", result, "\n";
  print "Total sum: ", y, "\n";
}