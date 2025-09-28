// <vc-preamble>
predicate IsDivisible(n: int, divisor: int)
    requires divisor != 0
{
    (n % divisor) == 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method PrimeNum(n: int) returns (result: bool)
    requires n >= 2
    ensures result == (forall k :: 2 <= k < n ==> !IsDivisible(n, k))
// </vc-spec>
// <vc-code>
{
    result := true;
    var i := 2;
    while i < n && result
        invariant 2 <= i <= n
        invariant result <==> (forall k :: 2 <= k < i ==> !IsDivisible(n, k))
    {
        if IsDivisible(n, i) {
            result := false;
        }
        i := i + 1;
    }
}
// </vc-code>
