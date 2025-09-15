// <vc-preamble>
function IsPrime(n: int) : bool
{
  n > 1 &&
  forall k :: 2 <= k < n ==> n % k != 0
}
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
predicate IsValidLength(len: int) { len >= 0 }
// </vc-helpers>

// <vc-spec>
method PrimeLength(s: string) returns (p : bool)

  ensures p <==> IsPrime(|s|)
// </vc-spec>
// <vc-code>
{
  var len := |s|;
  p := IsPrime(len);
}
// </vc-code>
