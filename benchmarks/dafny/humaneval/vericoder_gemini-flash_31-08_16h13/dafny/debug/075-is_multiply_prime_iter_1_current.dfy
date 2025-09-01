function Prime(p: nat) : bool
{
    p > 1 &&
    forall k :: 1 < k < p ==> p % k != 0
}

// <vc-helpers>
function isPrimeMultiply(n: nat, count: nat) : bool
    decreases n
{
    if count == 0 then n == 1
    else
        exists p: nat :: Prime(p) && n % p == 0 && isPrimeMultiply(n / p, count - 1)
}
// </vc-helpers>

// <vc-spec>
method is_multiply_prime(x: nat) returns (ans : bool)
    // pre-conditions-start
    requires x > 1
    // pre-conditions-end
    // post-conditions-start
    ensures ans <==> exists a: nat, b: nat, c: nat :: Prime(a) && Prime(b) && Prime(c) && x == a * b * c
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    ans := isPrimeMultiply(x, 3);
}
// </vc-code>

