predicate ValidInput(n: int, k: int) {
    n >= 0 && k >= 1
}

function MinValue(n: int, k: int): int
    requires ValidInput(n, k)
{
    var remainder := n % k;
    var complement := k - remainder;
    if remainder <= complement then remainder else complement
}

predicate IsCorrectResult(n: int, k: int, result: int) 
    requires ValidInput(n, k)
{
    result == MinValue(n, k) &&
    result >= 0 &&
    result < k
}

// <vc-helpers>
lemma MinValueProperties(n: int, k: int)
    requires ValidInput(n, k)
    ensures MinValue(n, k) >= 0
    ensures MinValue(n, k) < k
{
    var remainder := n % k;
    var complement := k - remainder;
    
    assert remainder >= 0 && remainder < k;
    assert complement > 0 && complement <= k;
    
    if remainder <= complement {
        assert MinValue(n, k) == remainder;
        assert remainder >= 0 && remainder < k;
    } else {
        assert MinValue(n, k) == complement;
        assert complement > 0 && complement <= k;
        assert complement < k;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
    requires ValidInput(n, k)
    ensures IsCorrectResult(n, k, result)
// </vc-spec>
// <vc-code>
{
    var remainder := n % k;
    var complement := k - remainder;
    
    if remainder <= complement {
        result := remainder;
    } else {
        result := complement;
    }
    
    MinValueProperties(n, k);
}
// </vc-code>

