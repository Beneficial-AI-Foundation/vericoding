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
/* helper modified by LLM (iteration 5): Fixed syntax errors and improved lemma structure */
lemma FactorizeLemma(n: int, factors: seq<int>) 
    requires n >= 2
    requires product(factors) == n
    requires forall i :: 0 <= i < |factors| ==> isPrime(factors[i])
    requires isNonDecreasing(factors)
    ensures exists factors' :: product(factors') == n && 
            (forall i :: 0 <= i < |factors'| ==> isPrime(factors'[i])) && 
            isNonDecreasing(factors')
{
}

function findNextFactor(n: int, start: int): (factor: int)
    requires n >= 2
    requires start >= 2
    ensures isPrime(factor)
    ensures factor >= start
    ensures n % factor == 0
    decreases n - start
{
    if isPrime(start) && n % start == 0 then
        start
    else
        findNextFactor(n, start + 1)
}

lemma FindNextFactorLemma(n: int, start: int)
    requires n >= 2
    requires start >= 2
    ensures exists k :: k >= start && isPrime(k) && n % k == 0
    decreases n - start
{
    if isPrime(start) && n % start == 0 {
    } else {
        FindNextFactorLemma(n, start + 1);
    }
}

lemma PrimeFactorizationExists(n: int)
    requires n >= 2
    ensures exists factors :: product(factors) == n && 
            (forall i :: 0 <= i < |factors| ==> isPrime(factors[i])) && 
            isNonDecreasing(factors)
    decreases n
{
    if isPrime(n) {
        assert product([n]) == n;
        assert forall i :: 0 <= i < |[n]| ==> isPrime([n][i]);
        assert isNonDecreasing([n]);
    } else {
        var factor := findNextFactor(n, 2);
        var remainder := n / factor;
        assert remainder >= 1;
        if remainder == 1 {
            assert product([factor]) == factor == n;
        } else {
            PrimeFactorizationExists(remainder);
            var subFactors :| product(subFactors) == remainder && 
                           (forall i :: 0 <= i < |subFactors| ==> isPrime(subFactors[i])) && 
                           isNonDecreasing(subFactors);
            var allFactors := [factor] + subFactors;
            ProductAppend([factor], product(subFactors));
            assert product(allFactors) == product([factor]) * product(subFactors) == factor * remainder == n;
            FactorizeLemma(remainder, subFactors);
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
/* code modified by LLM (iteration 5): Fixed syntax error by removing extra brace and improved implementation */
{
    if n <= 1 {
        factors := [];
    } else {
        factors := [];
        var current := n;
        var lastFactor := 2;
        
        while current > 1
            invariant current >= 1
            invariant product(factors) * current == n
            invariant forall i :: 0 <= i < |factors| ==> isPrime(factors[i])
            invariant isNonDecreasing(factors)
            invariant forall i :: 0 <= i < |factors| ==> factors[i] >= 2
            invariant lastFactor >= 2
            decreases current
        {
            var factor := findNextFactor(current, lastFactor);
            factors := factors + [factor];
            assert isNonDecreasing(factors) by {
                if |factors| > 1 {
                    assert factors[|factors|-2] <= factor;
                }
            };
            current := current / factor;
            lastFactor := factor;
            assert product(factors) * current == n by {
                ProductAppend(factors[0..|factors|-1], factor);
            };
        }
    }
}
// </vc-code>
