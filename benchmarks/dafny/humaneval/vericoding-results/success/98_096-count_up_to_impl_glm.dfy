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
  /* code modified by LLM (iteration 2): handle n<2 case separately */
  if n < 2 {
    primes := [];
  } else {
    var i := 2;
    primes := [];
    while i < n
      invariant 2 <= i <= n
      invariant forall p :: p in primes ==> IsPrime(p) && 2 <= p < n
      invariant forall p :: 2 <= p < i && IsPrime(p) ==> p in primes
    {
      if IsPrime(i) {
        primes := primes + [i];
      }
      i := i + 1;
    }
  }
}
// </vc-code>
