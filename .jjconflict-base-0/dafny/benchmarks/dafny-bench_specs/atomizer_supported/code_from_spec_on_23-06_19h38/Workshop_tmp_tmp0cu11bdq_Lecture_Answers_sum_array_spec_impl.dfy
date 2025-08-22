// ATOM 
function sumTo( a:array<int>, n:int ) : int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  reads a;
{
  if (n == 0) then 0 else sumTo(a, n-1) + a[n-1]
}

//IMPL 
method sum_array( a: array<int>) returns (sum: int)
  requires a != null;
  ensures sum == sumTo(a, a.Length);
{
  sum := 0;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length;
    invariant sum == sumTo(a, i);
  {
    sum := sum + a[i];
    i := i + 1;
  }
}