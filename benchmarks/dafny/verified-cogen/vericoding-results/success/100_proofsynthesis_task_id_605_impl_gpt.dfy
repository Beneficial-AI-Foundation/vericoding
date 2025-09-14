// <vc-preamble>
predicate IsDivisible(n: int, divisor: int)
    requires divisor != 0
{
    (n % divisor) == 0
}
// </vc-preamble>

// <vc-helpers>
function IsPrimeBySpec(n: int): bool
    requires n >= 2
{
    forall k: int :: 2 <= k && k < n ==> !IsDivisible(n, k)
}
// </vc-helpers>

// <vc-spec>
method PrimeNum(n: int) returns (result: bool)
    requires n >= 2
    ensures result == (forall k :: 2 <= k < n ==> !IsDivisible(n, k))
// </vc-spec>
// <vc-code>
{
  result := (forall k: int :: 2 <= k && k < n ==> !IsDivisible(n, k));
}
// </vc-code>
