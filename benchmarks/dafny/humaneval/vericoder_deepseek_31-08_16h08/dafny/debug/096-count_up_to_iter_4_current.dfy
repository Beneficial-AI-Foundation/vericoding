function IsPrime(n: int) : bool
{
  n > 1 && forall k :: 2 <= k < n ==> n % k != 0
}

// <vc-helpers>
lemma PrimeInRange(n: int, p: int)
  requires n >= 0
  requires 2 <= p < n && IsPrime(p)
  ensures p in [2..n)
{
}

lemma NotPrimeInRange(n: int, p: int)
  requires n >= 0
  requires 2 <= p < n && !IsPrime(p)
  ensures p in [2..n)
{
}

lemma PrimeInRangeSet(n: int, p: int)
  requires n >= 0
  requires 2 <= p < n && IsPrime(p)
  ensures p in [2..n)
{
}

lemma NotPrimeInRangeSet(n: int, p: int)
  requires n >= 0
  requires 2 <= p < n && !IsPrime(p)
  ensures p in [2..n)
{
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
  if n <= 2 {
    return primes;
  }
  
  var i := 2;
  while i < n
    invariant 2 <= i <= n
    invariant forall x :: x in primes ==> IsPrime(x)
    invariant forall x :: x in primes ==> x < n
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

