//ATOM
function countTo( a:array<bool>, n:int ) : int
 requires a != null
 requires 0 <= n && n <= a.Length
 reads a
{
 if (n == 0) then 0 else countTo(a, n-1) + (if a[n-1] then 1 else 0)
}


// SPEC

method CountTrue(a: array<bool>) returns (result: int)
  requires a != null
  ensures result == countTo(a, a.Length)
{
}
