// <vc-spec>
function sumTo( a:array<int>, n:int ) : int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  decreases n;
  reads a;
{
  if (n == 0) then 0 else sumTo(a, n-1) + a[n-1]
}

// <vc-helpers>
// </vc-helpers>

method ArraySum(a: array<int>) returns (result: int)
    ensures result == sumTo(a, a.Length)
// </vc-spec>
// <vc-code>
{
  result := 0;
  var i := 0;
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result == sumTo(a, i)
  {
    result := result + a[i];
    i := i + 1;
  }
}
// </vc-code>