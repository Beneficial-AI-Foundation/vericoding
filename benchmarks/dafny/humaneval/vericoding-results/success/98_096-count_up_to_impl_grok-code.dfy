// <vc-preamble>
function IsPrime(n: int) : bool
{
  n > 1 && forall k :: 2 <= k < n ==> n % k != 0
}
// </vc-preamble>

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
  /* code modified by LLM (iteration 4): Added condition to invariant and adjusted loop start to fix initial invariant violation for n < 2, then increment and check primes after. */
  primes := [];
  var i := 2;
  while i < n
    invariant if n < 2 then i == 2 else 2 <= i <= n
    invariant forall k :: 0 <= k < |primes| ==> IsPrime(primes[k])
    invariant forall k :: 0 <= k < |primes| ==> primes[k] < i
    invariant forall p :: 2 <= p < i && IsPrime(p) <==> p in primes
  {
    if IsPrime(i) {
      primes := primes + [i];
    }
    i := i + 1;
  }
}
// </vc-code>
