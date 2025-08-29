function IsPrime(n: int) : bool
{
  n > 1 &&
  forall k :: 2 <= k < n ==> n % k != 0
}

// <vc-helpers>
function CountDivisors(n: int, k: int) : int
  requires 1 <= k <= n
  decreases n - k
{
  if k == n then (if n % k == 0 then 1 else 0)
  else if n % k == 0 then 1 + CountDivisors(n, k + 1)
  else CountDivisors(n, k + 1)
}

lemma PrimeEquivalence(n: int)
  requires n > 1
  ensures IsPrime(n) <==> CountDivisors(n, 2) == 0
{
  if IsPrime(n) {
    assert forall k :: 2 <= k < n ==> n % k != 0;
    var k := 2;
    while k < n
      invariant 2 <= k <= n
      invariant forall i :: 2 <= i < k ==> n % i != 0
      decreases n - k
    {
      assert n % k != 0;
      k := k + 1;
    }
    var d := CountDivisors(n, 2);
    var i := 2;
    while i < n
      invariant 2 <= i <= n
      invariant forall j :: 2 <= j < i ==> n % j != 0
      decreases n - i
    {
      assert n % i != 0;
      i := i + 1;
    }
    assert d == 0;
  } else {
    var k :| 2 <= k < n && n % k == 0;
    var d := CountDivisors(n, 2);
    assert n % k == 0;
    assert k >= 2 && k <= n;
    if k == n {
      assert d == 0;
    } else {
      assert d >= 1;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method PrimeLength(s: string) returns (p : bool)
  // post-conditions-start
  ensures p <==> IsPrime(|s|)
  // post-conditions-end
// </vc-spec>
// <vc-code>
method PrimeLengthImpl(s: string) returns (p : bool)
  ensures p <==> IsPrime(|s|)
{
  if |s| <= 1 {
    return false;
  }
  var divisors := CountDivisors(|s|, 2);
  p := divisors == 0;
  PrimeEquivalence(|s|);
  assert p <==> IsPrime(|s|);
  return p;
}
// </vc-code>
