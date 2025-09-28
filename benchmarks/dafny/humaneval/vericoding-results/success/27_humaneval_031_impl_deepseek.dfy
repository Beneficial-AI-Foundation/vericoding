// <vc-preamble>

predicate is_prime_number(n: int)
{
    n >= 2 && forall k :: 2 <= k < n ==> n % k != 0
}
// </vc-preamble>

// <vc-helpers>
function {:opaque} divides(a: int, b: int): bool
    requires b != 0
{
    a % b == 0
}

lemma no_divisors_in_range(n: int, k: int)
    requires n >= 2 && 2 <= k < n
    ensures !divides(n, k) <==> n % k != 0
{
    reveal divides();
}

lemma prime_helper(n: int)
    requires n >= 2
    ensures is_prime_number(n) <==> (forall k :: 2 <= k < n ==> n % k != 0)
{
}
// </vc-helpers>

// <vc-spec>
method is_prime(n: int) returns (result: bool)
    ensures result <==> is_prime_number(n)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed verification by adding reveal statement */
    if (n < 2) {
        result := false;
        return;
    }
    
    var i := 2;
    while (i < n)
        invariant 2 <= i <= n
        invariant forall j :: 2 <= j < i ==> n % j != 0
    {
        no_divisors_in_range(n, i);
        if (n % i == 0) {
            result := false;
            return;
        }
        i := i + 1;
    }
    
    result := true;
}
// </vc-code>
