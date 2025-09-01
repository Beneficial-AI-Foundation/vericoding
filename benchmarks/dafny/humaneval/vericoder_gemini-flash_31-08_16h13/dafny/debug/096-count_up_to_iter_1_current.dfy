function IsPrime(n: int) : bool
{
  n > 1 && forall k :: 2 <= k < n ==> n % k != 0
}

// <vc-helpers>
function method IsPrime(n: int) : bool
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
  var primes_list: seq<int> := [];
  var i: int := 2;
  while i < n
    invariant 0 <= i <= n
    invariant forall p :: p in primes_list ==> IsPrime(p)
    invariant forall p :: p in primes_list ==> p < i
    invariant forall p :: 2 <= p < i && IsPrime(p) <==> p in primes_list
  {
    if IsPrime(i)
    {
      primes_list := primes_list + [i];
    }
    i := i + 1;
  }
  return primes_list;
}
// </vc-code>

