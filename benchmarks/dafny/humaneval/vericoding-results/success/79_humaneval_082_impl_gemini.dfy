// <vc-preamble>

predicate is_prime_number(n: int)
{
    n >= 2 && (forall k :: 2 <= k < n ==> n % k != 0)
}
// </vc-preamble>

// <vc-helpers>
method IsPrime(n: int) returns (res: bool)
    requires n >= 0
    ensures res <==> is_prime_number(n)
{
    if n < 2 {
        return false;
    }
    var k := 2;
    while k < n
        invariant 2 <= k <= n
        invariant forall i :: 2 <= i < k ==> n % i != 0
    {
        if n % k == 0 {
            return false;
        }
        k := k + 1;
    }
    return true;
}
// </vc-helpers>

// <vc-spec>
method prime_length(s: string) returns (result: bool)
    ensures result <==> is_prime_number(|s|)
// </vc-spec>
// <vc-code>
{
    result := IsPrime(|s|);
}
// </vc-code>
