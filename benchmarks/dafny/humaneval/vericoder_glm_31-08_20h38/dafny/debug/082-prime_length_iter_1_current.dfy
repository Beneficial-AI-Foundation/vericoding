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
  var n := |s|;
  if n < 2 {
    return false;
  }
  var i := 2;
  while i < n
    invariant 2 <= i <= n
    invariant forall k :: 2 <= k < i ==> n % k != 0
  {
    if n % i == 0 {
      return false;
    }
    i := i + 1;
  }
  return true;
}
// </vc-code>

