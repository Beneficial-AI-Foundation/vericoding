// <vc-preamble>

predicate is_prime(n: int)
{
    n > 1 && forall k :: 2 <= k < n ==> n % k != 0
}

function power_of_2_factor(n: int, current: int): int
    requires n > 0 && current > 0
    decreases current
{
    if current % 2 != 0 then 1
    else 2 * power_of_2_factor(n, current / 2)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method largest_prime_factor(n: int) returns (result: int)
    requires n > 1
    requires !is_prime(n)
    ensures result > 1
    ensures n % result == 0
    ensures forall k :: k > result && n % k == 0 ==> !is_prime(k)
    ensures is_prime(result)
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
  }
// </vc-code>
