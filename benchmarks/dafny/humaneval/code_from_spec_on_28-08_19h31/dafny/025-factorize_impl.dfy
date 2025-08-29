function prod(s: seq<int>) : int {
  if |s| == 0 then 1 else prod(s[..|s| - 1]) * s[|s| - 1]
}

// <vc-helpers>
function isPrime(n: nat): bool {
  if n < 2 then false
  else forall k :: 2 <= k < n ==> n % k != 0
}

lemma primeFactorization(n: nat)
  requires n > 0
  ensures exists fs: seq<nat> :: prod(fs) == n && forall i :: 0 <= i < |fs| ==> isPrime(fs[i])
{
  if n == 1 {
    assert prod([]) == 1;
    assert forall i :: 0 <= i < |[]| ==> isPrime([][i]);
  } else {
    var k := 2;
    while k * k <= n
      invariant k <= n
    {
      if n % k == 0 {
        assert isPrime(k);
        var m := n / k;
        primeFactorization(m);
        assert exists fs: seq<nat> :: prod(fs) == m && forall i :: 0 <= i < |fs| ==> isPrime(fs[i]);
        var fs :| prod(fs) == m && forall i :: 0 <= i < |fs| ==> isPrime(fs[i]);
        assert prod([k] + fs) == n;
        assert forall i :: 0 <= i < |[k] + fs| ==> isPrime(([k] + fs)[i]);
        return;
      }
      k := k + 1;
    }
    assert isPrime(n);
    assert prod([n]) == n;
    assert forall i :: 0 <= i < |[n]| ==> isPrime([n][i]);
  }
}
// </vc-helpers>

// <vc-spec>
method factorize(n: nat) returns (factors: seq<nat>)
  // pre-conditions-start
  requires n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures prod(factors) == n
  // post-conditions-end
// </vc-spec>
// <vc-code>
method Factorize(n: nat) returns (factors: seq<nat>)
  requires n > 0
  ensures prod(factors) == n
  ensures forall i :: 0 <= i < |factors| ==> isPrime(factors[i])
{
  factors := [];
  var remaining := n;
  var k := 2;
  while k * k <= remaining
    invariant remaining > 0
    invariant prod(factors) * remaining == n
    invariant forall i :: 0 <= i < |factors| ==> isPrime(factors[i])
  {
    while remaining % k == 0
      invariant remaining > 0
      invariant prod(factors) * remaining == n
      invariant forall i :: 0 <= i < |factors| ==> isPrime(factors[i])
    {
      factors := factors + [k];
      remaining := remaining / k;
      assert isPrime(k);
    }
    k := k + 1;
  }
  if remaining > 1 {
    factors := factors + [remaining];
    assert isPrime(remaining);
  }
}
// </vc-code>
