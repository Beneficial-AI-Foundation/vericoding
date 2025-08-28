// <vc-helpers>
lemma DivisorExists(n: int, k: int)
    requires n >= 2 && 2 <= k < n && n % k == 0
    ensures exists d :: 2 <= d < n && n % d == 0
{
}

lemma NoDivisorMeansNone(n: int, upper: int)
    requires n >= 2 && upper >= 2
    requires forall k :: 2 <= k < upper ==> n % k != 0
    requires upper >= n
    ensures forall k :: 2 <= k < n ==> n % k != 0
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method IsNonPrime(n: int) returns (result: bool)
    requires n >= 2
    ensures result <==> (exists k :: 2 <= k < n && n % k == 0)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    var i := 2;
    while i < n
        invariant 2 <= i <= n
        invariant forall k :: 2 <= k < i ==> n % k != 0
    {
        if n % i == 0 {
            DivisorExists(n, i);
            return true;
        }
        i := i + 1;
    }
    NoDivisorMeansNone(n, i);
    return false;
}
// </vc-code>
