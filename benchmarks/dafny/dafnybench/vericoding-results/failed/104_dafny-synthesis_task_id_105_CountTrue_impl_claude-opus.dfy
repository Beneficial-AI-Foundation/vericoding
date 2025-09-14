function countTo( a:array<bool>, n:int ) : int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  decreases n;
  reads a;
{
  if (n == 0) then 0 else countTo(a, n-1) + (if a[n-1] then 1 else 0)
}

// <vc-helpers>
lemma CountToLemma(a: array<bool>, n: int)
    requires 0 <= n < a.Length
    ensures countTo(a, n+1) == countTo(a, n) + (if a[n] then 1 else 0)
{
    // This lemma follows directly from the definition of countTo
}
// </vc-helpers>

// <vc-spec>
method CountTrue(a: array<bool>) returns (result: int)
    requires a != null
    ensures result == countTo(a, a.Length)
// </vc-spec>
// <vc-code>
{
    var i := 0;
    result := 0;
    
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant result == countTo(a, i)
    {
        if a[i] {
            result := result + 1;
        }
        CountToLemma(a, i);
        i := i + 1;
    }
}
// </vc-code>

