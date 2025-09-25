// <vc-preamble>
predicate ValidInput(prices: seq<int>)
{
    |prices| >= 1 && |prices| <= 100 &&
    forall p :: p in prices ==> p >= 1 && p <= 10000000
}

function Sum(prices: seq<int>): int
{
    if |prices| == 0 then 0
    else prices[0] + Sum(prices[1..])
}

function MinUniformPrice(prices: seq<int>): int
    requires ValidInput(prices)
{
    (Sum(prices) + |prices| - 1) / |prices|
}

predicate CorrectResult(prices: seq<int>, uniform_price: int)
    requires ValidInput(prices)
{
    uniform_price >= 1 &&
    |prices| * uniform_price >= Sum(prices) &&
    (uniform_price > 1 ==> |prices| * (uniform_price - 1) < Sum(prices))
}
// </vc-preamble>

// <vc-helpers>
lemma SubsequenceProperty(prices: seq<int>)
    requires forall p :: p in prices ==> p >= 1
    requires |prices| > 0
    ensures prices[0] >= 1
    ensures forall p :: p in prices[1..] ==> p >= 1
{
    assert prices[0] in prices;
    forall p | p in prices[1..]
    ensures p >= 1
    {
        assert exists i :: 1 <= i < |prices| && prices[i] == p;
        assert p in prices;
    }
}

lemma SumNonNegative(prices: seq<int>)
    requires forall p :: p in prices ==> p >= 1
    ensures Sum(prices) >= |prices|
{
    if |prices| == 0 {
        assert Sum(prices) == 0;
        assert |prices| == 0;
    } else {
        SubsequenceProperty(prices);
        SumNonNegative(prices[1..]);
        assert Sum(prices[1..]) >= |prices[1..]|;
        assert |prices[1..]| == |prices| - 1;
        assert Sum(prices) == prices[0] + Sum(prices[1..]);
        assert Sum(prices) >= 1 + (|prices| - 1);
        assert Sum(prices) >= |prices|;
    }
}

lemma CeilDivisionCorrect(total: int, n: int)
    requires n >= 1
    requires total >= 0
    ensures var result := (total + n - 1) / n;
            n * result >= total &&
            (result > 0 ==> n * (result - 1) < total)
{
    var result := (total + n - 1) / n;
    if total == 0 {
        assert result == 0;
        assert n * result >= total;
    } else {
        assert total > 0;
        assert result >= 1;
        assert result > 0;
        
        // For integer division, we have: a/b * b <= a < (a/b + 1) * b
        // So: (total + n - 1) / n * n <= total + n - 1 < ((total + n - 1) / n + 1) * n
        // Which gives us: result * n <= total + n - 1 < (result + 1) * n
        // From result * n <= total + n - 1, we get: result * n <= total + n - 1 < total + n
        // From (result + 1) * n > total + n - 1, we get: result * n + n > total + n - 1
        // So: result * n > total - 1, which means result * n >= total (since they're integers)
        
        // The key insight is that result * n >= total always holds for ceiling division
        assert result * n >= total;
        
        // For the second part, if result > 1, then (result - 1) * n < total
        if result > 1 {
            // Since result = ceil(total/n), we have (result-1) < total/n <= result
            // So (result-1) * n < total
            assert (result - 1) * n < total;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method FindMinUniformPrice(prices: seq<int>) returns (uniform_price: int)
    requires ValidInput(prices)
    ensures CorrectResult(prices, uniform_price)
    ensures uniform_price == MinUniformPrice(prices)
// </vc-spec>
// <vc-code>
{
    var total := Sum(prices);
    var n := |prices|;
    
    SumNonNegative(prices);
    assert total >= n;
    assert total >= 0;
    
    uniform_price := (total + n - 1) / n;
    
    CeilDivisionCorrect(total, n);
    assert n * uniform_price >= total;
    assert uniform_price > 0 ==> n * (uniform_price - 1) < total;
    assert uniform_price >= 1;
}
// </vc-code>
