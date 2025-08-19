method M(N: int, a: array<int>) returns (sum: int, max: int)
 requires 0 <= N && a.Length == N && (forall k :: 0 <= k && k < N ==> 0 <= a[k])
 ensures sum <= N * max
{
  /* code modified by LLM (iteration 1): Complete implementation that computes actual sum and max */
  sum := 0;
  max := 0;
  
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant sum == (if i == 0 then 0 else sum_of_range(a, 0, i))
    invariant max == (if i == 0 then 0 else max_of_range(a, 0, i))
    invariant sum <= i * max
  {
    sum := sum + a[i];
    if a[i] > max {
      max := a[i];
    }
    i := i + 1;
  }
}

/* code modified by LLM (iteration 1): Added helper functions for specification */
function sum_of_range(a: array<int>, start: int, end: int): int
  reads a
  requires 0 <= start <= end <= a.Length
{
  if start == end then 0
  else a[start] + sum_of_range(a, start + 1, end)
}

function max_of_range(a: array<int>, start: int, end: int): int
  reads a
  requires 0 <= start < end <= a.Length
  requires forall k :: start <= k < end ==> 0 <= a[k]
{
  if start + 1 == end then a[start]
  else
    var rest_max := max_of_range(a, start + 1, end);
    if a[start] >= rest_max then a[start] else rest_max
}

//IMPL 
method Main()
{
 /* code modified by LLM (iteration 1): Added initialization to ensure array elements satisfy the precondition of method M */
 var a := new int[10];
 a[0] := 9;
 a[1] := 5;
 a[2] := 0;
 a[3] := 2;
 a[4] := 7;
 a[5] := 3;
 a[6] := 2;
 a[7] := 1;
 a[8] := 10;
 a[9] := 6;
 var s, m := M(10, a);
 print "N = ", a.Length, " sum = ", s, " max = ", m, "\n";
}