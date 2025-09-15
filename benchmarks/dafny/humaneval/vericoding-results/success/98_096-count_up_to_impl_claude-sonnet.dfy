// <vc-preamble>
function IsPrime(n: int) : bool
{
  n > 1 && forall k :: 2 <= k < n ==> n % k != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Fixed syntax for set comprehension */
function PrimesUpTo(n: int): seq<int>
  requires n >= 0
{
  if n <= 2 then []
  else PrimesUpTo(n-1) + (if IsPrime(n-1) then [n-1] else [])
}
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
  /* code modified by LLM (iteration 3): Fixed loop invariant to handle case when n < 2 */
  primes := [];
  if n <= 2 {
    return;
  }
  var i := 2;
  while i < n
    invariant 2 <= i <= n
    invariant forall j :: 0 <= j < |primes| ==> IsPrime(primes[j])
    invariant forall j :: 0 <= j < |primes| ==> primes[j] < i
    invariant forall p :: 2 <= p < i && IsPrime(p) ==> p in primes
    invariant forall p :: p in primes ==> 2 <= p < i && IsPrime(p)
  {
    if IsPrime(i) {
      primes := primes + [i];
    }
    i := i + 1;
  }
}
// </vc-code>
