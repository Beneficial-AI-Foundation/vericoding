// <vc-preamble>
function IsPrime(n: int) : bool
{
  n > 1 &&
  forall k :: 2 <= k < n ==> n % k != 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method PrimeLength(s: string) returns (p : bool)

  ensures p <==> IsPrime(|s|)
// </vc-spec>
// <vc-code>
{
  p := IsPrime(|s|);
}
// </vc-code>
