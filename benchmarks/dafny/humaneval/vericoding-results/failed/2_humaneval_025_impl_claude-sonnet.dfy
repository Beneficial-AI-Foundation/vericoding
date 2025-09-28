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
/* helper modified by LLM (iteration 5): added lemmas for prime properties and invariant maintenance */
lemma ProductPositive(factors: seq<int>)
    requires forall i :: 0 <= i < |factors| ==> factors[i] > 0
    ensures product(factors) > 0
{
    if |factors| == 0 {
        assert product(factors) == 1;
    } else {
        ProductPositive(factors[1..]);
        assert product(factors) == factors[0] * product(factors[1..]);
        assert factors[0] > 0 && product(factors[1..]) > 0;
    }
}

lemma ProductOne(factors: seq<int>)
    requires |factors| == 0
    ensures product(factors) == 1
{
}

lemma DivisionDecreases(a: int, b: int)
    requires a > 1 && b >= 2 && a % b == 0
    ensures a / b < a
{
    assert a == (a / b) * b;
    assert a / b >= 1;
    assert b >= 2;
    assert (a / b) * b >= 2 * (a / b);
    assert a >= 2 * (a / b);
    assert a / b <= a / 2;
    assert a / b < a;
}

lemma RemainingIsPrime(n: int, candidate: int)
    requires n > 1
    requires candidate >= 2
    requires candidate * candidate > n
    requires forall k :: 2 <= k < candidate ==> n % k != 0
    ensures isPrime(n)
{
    assert n >= 2;
    forall k | 2 <= k < n
        ensures n % k != 0
    {
        if k < candidate {
            assert n % k != 0;
        } else {
            assert k >= candidate;
            assert k < n;
            if n % k == 0 {
                assert n == (n / k) * k;
                assert n / k >= 1;
                if n / k == 1 {
                    assert n == k;
                    assert false;
                }
                assert n / k >= 2;
                assert k >= candidate && n / k >= 2;
                assert k * (n / k) >= candidate * 2;
                assert n >= 2 * candidate;
                assert candidate * candidate <= candidate * 2;
                assert candidate <= 2;
                if candidate == 2 {
                    assert k >= 2 && n / k >= 2;
                    assert n >= 4;
                    assert 4 > 4;
                    assert false;
                }
                assert false;
            }
        }
    }
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
    /* code modified by LLM (iteration 5): simplified loop structure and fixed invariant maintenance */
    if n <= 1 {
        factors := [];
        return;
    }
    
    factors := [];
    var remaining := n;
    var candidate := 2;
    
    while remaining > 1
        invariant remaining >= 1
        invariant candidate >= 2
        invariant product(factors) * remaining == n
        invariant forall i :: 0 <= i < |factors| ==> isPrime(factors[i])
        invariant isNonDecreasing(factors)
        invariant forall i :: 0 <= i < |factors| ==> factors[i] >= 2
        invariant |factors| > 0 ==> candidate >= factors[|factors|-1]
        invariant forall k :: 2 <= k < candidate ==> remaining % k != 0
        decreases remaining
    {
        if remaining % candidate == 0 {
            factors := factors + [candidate];
            ProductAppend(factors[..|factors|-1], candidate);
            DivisionDecreases(remaining, candidate);
            remaining := remaining / candidate;
        } else {
            if candidate * candidate > remaining {
                RemainingIsPrime(remaining, candidate);
                factors := factors + [remaining];
                ProductAppend(factors[..|factors|-1], remaining);
                remaining := 1;
            } else {
                candidate := candidate + 1;
            }
        }
    }
}
// </vc-code>
