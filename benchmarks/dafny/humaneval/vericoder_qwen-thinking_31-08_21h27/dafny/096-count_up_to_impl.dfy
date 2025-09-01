function IsPrime(n: int) : bool
{
  n > 1 && forall k :: 2 <= k < n ==> n % k != 0
}

// <vc-helpers>
function IsPrime(n: int) : bool
{
  n > 1 && forall k :: 2 <= k < n ==> n % k != 0
}
// </vc-helpers>

// <vc-spec>
method CountUpTo(n: int) returns (primes: seq<int>)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures forall i :: 0 <= i < |primes| ==> IsPrime(primes[i])
  ensures forall i :: 0 <= i < |primes| ==> primes[i] < n
  ensures forall p :: 2 <= p < n && IsPrime(p) <==> p in primes
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
    primes := [];
    var i := 2;
    while i < n
        invariant forall p :: 2 <= p < i && IsPrime(p) ==> p in primes
        invariant forall p :: 2 <= p < i && p in primes ==> IsPrime(p)
        decreases n - i
    {
        if IsPrime(i) {
            primes := primes + [i];
        }
        i := i + 1;
    }
    return primes;
}
// </vc-code>

