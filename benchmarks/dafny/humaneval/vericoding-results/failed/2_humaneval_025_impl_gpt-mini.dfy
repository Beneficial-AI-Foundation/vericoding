// <vc-preamble>
predicate isPrime(n: int)
{
    n >= 2 && forall k :: 2 <= k < n ==> n % k != 0
}

function product(factors: seq<int>): int
{
    if |factors| == 0 then 1
    else factors[0] * product(factors[1..])
}

predicate isNonDecreasing(factors: seq<int>)
{
    forall i, j :: 0 <= i < j < |factors| ==> factors[i] <= factors[j]
}
lemma ProductAppend(factors: seq<int>, x: int)
    ensures product(factors + [x]) == product(factors) * x
{
    if |factors| == 0 {
        assert factors + [x] == [x];
        assert product([x]) == x * product([]) == x * 1 == x;
        assert product(factors) * x == 1 * x == x;
    } else {
        assert (factors + [x])[0] == factors[0];
        assert (factors + [x])[1..] == factors[1..] + [x];
        ProductAppend(factors[1..], x);
        assert product(factors[1..] + [x]) == product(factors[1..]) * x;
        assert product(factors + [x]) == factors[0] * product(factors[1..] + [x]);
        assert product(factors + [x]) == factors[0] * product(factors[1..]) * x;
        assert product(factors + [x]) == product(factors) * x;
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): SmallestDivisorFrom kept, comment added */
method SmallestDivisorFrom(n: int, start: int) returns (d: int)
    requires n >= 2
    requires 2 <= start <= n
    ensures start <= d <= n
    ensures n % d == 0
    ensures forall k :: start <= k < d ==> n % k != 0
{
  var k := start;
  while k < n
    invariant start <= k <= n
    invariant forall t :: start <= t < k ==> n % t != 0
    decreases n - k
  {
    if n % k == 0 {
      d := k;
      return;
    }
    k := k + 1;
  }
  d := n;
}

// </vc-helpers>

// <vc-spec>
method factorize(n: int) returns (factors: seq<int>)
    ensures n <= 1 ==> |factors| == 0
    ensures n > 1 ==> product(factors) == n
    ensures forall i :: 0 <= i < |factors| ==> isPrime(factors[i])
    ensures isNonDecreasing(factors)
    ensures forall i :: 0 <= i < |factors| ==> factors[i] >= 2
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): use min(nextStart, rem) when calling SmallestDivisorFrom to satisfy precondition */
  if n <= 1 {
    factors := [];
    return;
  }
  var rem := n;
  factors := [];
  var nextStart := 2;
  while rem > 1
    invariant rem >= 1
    invariant product(factors) * rem == n
    invariant forall i :: 0 <= i < |factors| ==> isPrime(factors[i])
    invariant isNonDecreasing(factors)
    invariant forall i :: 0 <= i < |factors| ==> factors[i] >= 2
    invariant (|factors| > 0) ==> nextStart == factors[|factors|-1]
    invariant (|factors| == 0) ==> nextStart == 2
    invariant forall t :: 2 <= t < nextStart ==> rem % t != 0
    decreases rem
  {
    var startArg := if nextStart <= rem then nextStart else rem;
    var d := SmallestDivisorFrom(rem, startArg);
    // rem has no divisors < startArg (invariant) and SmallestDivisorFrom ensures none in [startArg, d)
    assert forall t :: 2 <= t < d ==> rem % t != 0;
    // prove d is prime: show no r in 2..d-1 divides d
    var r := 2;
    while r < d
      invariant 2 <= r <= d
    {
      if d % r == 0 {
        // from rem % d == 0 and d % r == 0 deduce rem % r == 0
        var td := d / r;
        var q := rem / d;
        assert d == r * td;
        assert rem == d * q;
        assert rem == r * (td * q);
        assert rem % r == 0;
        // contradicts the fact rem has no divisors < d
        assert rem % r != 0;
      }
      r := r + 1;
    }
    // d is prime, append and update remainder
    var prev := factors[0..|factors|-1];
    factors := prev + [d];
    ProductAppend(prev, d);
    rem := rem / d;
    nextStart := d;
  }
}

// </vc-code>
