// <vc-preamble>
predicate IsDivisible(n: int, divisor: int)
    requires divisor != 0
{
    (n % divisor) == 0
}
// </vc-preamble>

// <vc-helpers>
lemma NonZeroFromAtLeastTwo(k: int)
  ensures 2 <= k ==> k != 0
{
}

predicate ProperDivisor(n: int, k: int)
{
  2 <= k < n
}
// </vc-helpers>

// <vc-spec>
method IsNonPrime(n: int) returns (result: bool)
    requires n >= 2
    ensures result == (exists k :: 2 <= k < n && IsDivisible(n, k))
// </vc-spec>
// <vc-code>
{
  result := exists k :: 2 <= k < n && IsDivisible(n, k);
}
// </vc-code>
