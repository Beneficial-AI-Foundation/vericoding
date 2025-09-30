

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsNonPrime(n: int) returns (result: bool)
    requires n >= 2
    ensures result <==> (exists k :: 2 <= k < n && n % k == 0)
// </vc-spec>
// <vc-code>
{
    var i := 2;
    while i < n
        invariant 2 <= i <= n
        invariant forall k :: 2 <= k < i ==> n % k != 0
    {
        if n % i == 0 {
            result := true;
            return;
        }
        i := i + 1;
    }
    result := false;
}
// </vc-code>

