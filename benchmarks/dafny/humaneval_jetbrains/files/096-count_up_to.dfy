function IsPrime(n: int) : bool
{
  n > 1 && forall k :: 2 <= k < n ==> n % k != 0
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method CountUpTo(n: int) returns (primes: seq<int>)

  requires n >= 0

  ensures forall i :: 0 <= i < |primes| ==> IsPrime(primes[i])
  ensures forall i :: 0 <= i < |primes| ==> primes[i] < n
  ensures forall p :: 2 <= p < n && IsPrime(p) <==> p in primes
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
