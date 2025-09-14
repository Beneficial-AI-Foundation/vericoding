function sumTo( a:array<int>, n:int ) : int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  decreases n;
  reads a;
{
  if (n == 0) then 0 else sumTo(a, n-1) + a[n-1]
}

// <vc-helpers>
function sumTo_helper(a: array<int>, n: int): int
  requires a != null
  requires 0 <= n && n <= a.Length
  decreases n
  reads a
{
  if n == 0 then 0 else sumTo_helper(a, n - 1) + a[n - 1]
}

lemma SumToEquivalent(a: array<int>, n: int)
  requires a != null
  requires 0 <= n <= a.Length
  ensures sumTo(a, n) == sumTo_helper(a, n)
{
  if n > 0 {
    SumToEquivalent(a, n - 1);
  }
}
// </vc-helpers>

// <vc-spec>
method ArraySum(a: array<int>) returns (result: int)
    ensures result == sumTo(a, a.Length)
// </vc-spec>
// <vc-code>
{
    var n := a.Length;
    var currentSum := 0;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant currentSum == sumTo_helper(a, i)
    {
        currentSum := currentSum + a[i];
        i := i + 1;
    }
    SumToEquivalent(a, a.Length);
    return currentSum;
}
// </vc-code>

