// <vc-preamble>
function IsPrime(n: int) : bool
{
  n > 1 &&
  forall k :: 2 <= k < n ==> n % k != 0
}
// </vc-preamble>

// <vc-helpers>
function Divides(n: int, k: int): bool { k != 0 && n % k == 0 }
function IsPrimeLen(s: string): bool { IsPrime(|s|) }
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
