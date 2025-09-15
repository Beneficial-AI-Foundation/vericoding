// <vc-preamble>
function Prime(p: nat) : bool
{
    p > 1 &&
    forall k :: 1 < k < p ==> p % k != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified to use imperative factorization approach */
function IsPrime(n: nat): bool
{
    n > 1 && forall k :: 1 < k < n ==> n % k != 0
}

method GetPrimeFactors(x: nat) returns (factors: seq<nat>)
    requires x > 1
    ensures forall i :: 0 <= i < |factors| ==> IsPrime(factors[i])
    ensures forall i :: 0 <= i < |factors| ==> factors[i] > 1
{
    factors := [];
    var temp := x;
    var p := 2;
    
    while p <= temp
        invariant p >= 2
        invariant temp >= 1
        invariant forall i :: 0 <= i < |factors| ==> IsPrime(factors[i])
        decreases temp
    {
        if temp % p == 0 && IsPrime(p) {
            factors := factors + [p];
            temp := temp / p;
        } else {
            p := p + 1;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method is_multiply_prime(x: nat) returns (ans : bool)

    requires x > 1

    ensures ans <==> exists a: nat, b: nat, c: nat :: Prime(a) && Prime(b) && Prime(c) && x == a * b * c
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): use helper method to get prime factors and check count */
{
    var primeFactors := GetPrimeFactors(x);
    ans := |primeFactors| == 3;
}
// </vc-code>
