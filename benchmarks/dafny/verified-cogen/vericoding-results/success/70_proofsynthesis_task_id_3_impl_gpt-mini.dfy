// <vc-preamble>
predicate IsDivisible(n: int, divisor: int)
    requires divisor != 0
{
    (n % divisor) == 0
}
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }

lemma DivisorWitness(n: int, k: int)
    requires 2 <= k < n && IsDivisible(n, k)
    ensures exists k' :: 2 <= k' < n && IsDivisible(n, k')
{
}

// </vc-helpers>

// <vc-spec>
method IsNonPrime(n: int) returns (result: bool)
    requires n >= 2
    ensures result == (exists k :: 2 <= k < n && IsDivisible(n, k))
// </vc-spec>
// <vc-code>
{
  var k := 2;
  result := false;
  while k < n
    invariant 2 <= k <= n
    invariant result <==> (exists k' :: 2 <= k' < k && IsDivisible(n, k'))
    decreases n - k
  {
    if IsDivisible(n, k) {
      result := true;
      break;
    }
    k := k + 1;
  }
}

// </vc-code>
