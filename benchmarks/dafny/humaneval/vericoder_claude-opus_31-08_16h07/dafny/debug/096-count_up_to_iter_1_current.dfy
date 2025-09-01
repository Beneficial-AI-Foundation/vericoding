function IsPrime(n: int) : bool
{
  n > 1 && forall k :: 2 <= k < n ==> n % k != 0
}

// <vc-helpers>
lemma IsPrimeImpliesGreaterThanOne(n: int)
  requires IsPrime(n)
  ensures n > 1
{
}

method IsPrimeMethod(n: int) returns (result: bool)
  ensures result == IsPrime(n)
{
  if n <= 1 {
    return false;
  }
  
  var k := 2;
  while k < n
    invariant 2 <= k <= n
    invariant forall j :: 2 <= j < k ==> n % j != 0
  {
    if n % k == 0 {
      return false;
    }
    k := k + 1;
  }
  
  return true;
}

lemma PrimesInRangeComplete(primes: seq<int>, n: int)
  requires n >= 0
  requires forall i :: 0 <= i < |primes| ==> IsPrime(primes[i])
  requires forall i :: 0 <= i < |primes| ==> primes[i] < n
  requires forall i, j :: 0 <= i < j < |primes| ==> primes[i] < primes[j]
  requires forall p :: 2 <= p < n && IsPrime(p) ==> p in primes
  ensures forall p :: 2 <= p < n && IsPrime(p) <==> p in primes
{
  forall p | 2 <= p < n
    ensures IsPrime(p) <==> p in primes
  {
    if p in primes {
      var idx :| 0 <= idx < |primes| && primes[idx] == p;
      assert IsPrime(primes[idx]);
    }
  }
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
    invariant 2 <= i <= n
    invariant forall j :: 0 <= j < |primes| ==> IsPrime(primes[j])
    invariant forall j :: 0 <= j < |primes| ==> primes[j] < i
    invariant forall j, k :: 0 <= j < k < |primes| ==> primes[j] < primes[k]
    invariant forall p :: 2 <= p < i && IsPrime(p) ==> p in primes
    invariant forall p :: p in primes ==> 2 <= p < i && IsPrime(p)
  {
    var isPrime := IsPrimeMethod(i);
    if isPrime {
      primes := primes + [i];
    }
    i := i + 1;
  }
  
  PrimesInRangeComplete(primes, n);
}
// </vc-code>

