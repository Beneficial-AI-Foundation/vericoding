function IsPrime(n: int) : bool
{
  n > 1 &&
  forall k :: 2 <= k < n ==> n % k != 0
}

// <vc-helpers>
// No helpers needed
// </vc-helpers>

// <vc-spec>
method PrimeLength(s: string) returns (p : bool)
  // post-conditions-start
  ensures p <==> IsPrime(|s|)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  p := |s| > 1 && (forall k :: 2 <= k < |s| ==> |s| % k != 0);
}
// </vc-code>

