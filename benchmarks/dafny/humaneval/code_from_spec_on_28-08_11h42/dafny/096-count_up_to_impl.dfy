function IsPrime(n: int) : bool
{
  n > 1 && forall k :: 2 <= k < n ==> n % k != 0
}

// <vc-helpers>
lemma PrimeInvariant(primes: seq<int>, i: int)
  requires forall j :: 0 <= j < |primes| ==> IsPrime(primes[j])
  requires forall j :: 0 <= j < |primes| ==> primes[j] < i
  requires forall p :: 2 <= p < i && IsPrime(p) ==> p in primes
  requires i >= 0
  requires IsPrime(i)
  ensures forall j :: 0 <= j < |primes + [i]| ==> IsPrime((primes + [i])[j])
  ensures forall j :: 0 <= j < |primes + [i]| ==> (primes + [i])[j] < i + 1
  ensures forall p :: 2 <= p < i + 1 && IsPrime(p) ==> p in (primes + [i])
{
  var newPrimes := primes + [i];
  
  forall j | 0 <= j < |newPrimes|
    ensures IsPrime(newPrimes[j])
  {
    if j < |primes| {
      assert newPrimes[j] == primes[j];
    } else {
      assert j == |primes|;
      assert newPrimes[j] == i;
    }
  }
  
  forall j | 0 <= j < |newPrimes|
    ensures newPrimes[j] < i + 1
  {
    if j < |primes| {
      assert newPrimes[j] == primes[j];
    } else {
      assert newPrimes[j] == i;
    }
  }
  
  forall p | 2 <= p < i + 1 && IsPrime(p)
    ensures p in newPrimes
  {
    if p < i {
      assert p in primes;
      assert p in newPrimes;
    } else {
      assert p == i;
      assert p in newPrimes;
    }
  }
}

lemma NonPrimeInvariant(primes: seq<int>, i: int)
  requires forall j :: 0 <= j < |primes| ==> IsPrime(primes[j])
  requires forall j :: 0 <= j < |primes| ==> primes[j] < i
  requires forall p :: 2 <= p < i && IsPrime(p) ==> p in primes
  requires i >= 0
  requires !IsPrime(i)
  ensures forall j :: 0 <= j < |primes| ==> IsPrime(primes[j])
  ensures forall j :: 0 <= j < |primes| ==> primes[j] < i + 1
  ensures forall p :: 2 <= p < i + 1 && IsPrime(p) ==> p in primes
{
  forall p | 2 <= p < i + 1 && IsPrime(p)
    ensures p in primes
  {
    if p < i {
      assert p in primes;
    } else {
      assert p == i;
      assert !IsPrime(i);
      assert false;
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
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < |primes| ==> IsPrime(primes[j])
    invariant forall j :: 0 <= j < |primes| ==> primes[j] < i
    invariant forall p :: 2 <= p < i && IsPrime(p) ==> p in primes
  {
    if IsPrime(i) {
      PrimeInvariant(primes, i);
      primes := primes + [i];
    } else {
      NonPrimeInvariant(primes, i);
    }
    i := i + 1;
  }
  
  forall p | 2 <= p < n && IsPrime(p)
    ensures p in primes
  {
    assert 2 <= p < i;
  }
  
  forall p | p in primes
    ensures 2 <= p < n && IsPrime(p)
  {
    var j :| 0 <= j < |primes| && primes[j] == p;
    assert IsPrime(p);
    assert p < i;
    assert p < n;
    assert p >= 2;
  }
}
// </vc-code>
