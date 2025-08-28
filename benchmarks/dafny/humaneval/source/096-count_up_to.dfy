function IsPrime(n: int) : bool
{
  n > 1 && forall k :: 2 <= k < n ==> n % k != 0
}
// pure-end
method CountUpTo(n: int) returns (primes: seq<int>)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures forall i :: 0 <= i < |primes| ==> IsPrime(primes[i])
  ensures forall i :: 0 <= i < |primes| ==> primes[i] < n
  ensures forall p :: 2 <= p < n && IsPrime(p) <==> p in primes
  // post-conditions-end
{
  // impl-start
  primes := [];
  if n <= 2 { return; }
  var i := 2;
  while i < n
    // invariants-start
    invariant 2 <= i <= n
    invariant forall j :: 0 <= j < |primes| ==> IsPrime(primes[j])
    invariant forall j :: 0 <= j < |primes| ==> 2 <= primes[j] < i
    invariant forall p :: 2 <= p < i && IsPrime(p) <==> p in primes
    invariant forall j, k :: 0 <= j < k < |primes| ==> primes[j] < primes[k]
    // invariants-end
  {
    if IsPrime(i) {
      primes := primes + [i];
    }
    i := i + 1;
  }
  // impl-end
}
