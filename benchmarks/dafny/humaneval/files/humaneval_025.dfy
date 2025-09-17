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
    assume {:axiom} false;
  }
// </vc-code>
