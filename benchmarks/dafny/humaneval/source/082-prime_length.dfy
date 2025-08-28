function IsPrime(n: int) : bool
{
  n > 1 &&
  forall k :: 2 <= k < n ==> n % k != 0
}
// pure-end
method PrimeLength(s: string) returns (p : bool)
  // post-conditions-start
  ensures p <==> IsPrime(|s|)
  // post-conditions-end
{
  // impl-start
  return IsPrime(|s|);
  // impl-end
}
