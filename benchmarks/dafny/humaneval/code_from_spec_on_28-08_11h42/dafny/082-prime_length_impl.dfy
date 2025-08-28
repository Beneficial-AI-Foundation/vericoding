function IsPrime(n: int) : bool
{
  n > 1 &&
  forall k :: 2 <= k < n ==> n % k != 0
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method PrimeLength(s: string) returns (p : bool)
  // post-conditions-start
  ensures p <==> IsPrime(|s|)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  p := IsPrime(|s|);
}
// </vc-code>
