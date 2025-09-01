function IsPrime(n: int) : bool
{
  n > 1 && forall k :: 2 <= k < n ==> n % k != 0
}

// <vc-helpers>

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
  var result := [];
  var i := 2;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 2 <= k < i ==> (IsPrime(k) <==> k in result)
    invariant forall j :: 0 <= j < |result| ==> IsPrime(result[j]) && 2 <= result[j] < i
    invariant forall j :: 0 <= j < |result| - 1 ==> result[j] < result[j+1]
  {
    if IsPrime(i) {
      result := result + [i];
    }
    i := i + 1;
  }
  primes := result;
}
// </vc-code>

