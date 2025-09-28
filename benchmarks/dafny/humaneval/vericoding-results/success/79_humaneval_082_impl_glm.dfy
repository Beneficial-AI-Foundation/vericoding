// <vc-preamble>

predicate is_prime_number(n: int)
{
    n >= 2 && (forall k :: 2 <= k < n ==> n % k != 0)
}
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method prime_length(s: string) returns (result: bool)
    ensures result <==> is_prime_number(|s|)
// </vc-spec>
// <vc-code>
{
  result := is_prime_number(|s|);
}
// </vc-code>
