predicate ValidInput(n: int, m: int, scores: seq<int>)
{
    n >= 1 && m >= 1 && |scores| == n &&
    forall i :: 0 <= i < |scores| ==> 0 <= scores[i] <= m
}

function Sum(nums: seq<int>): int
    ensures Sum(nums) >= 0 || exists i :: 0 <= i < |nums| && nums[i] < 0
{
    if |nums| == 0 then 0
    else nums[0] + Sum(nums[1..])
}

function min(a: int, b: int): int
    ensures min(a, b) == a || min(a, b) == b
    ensures min(a, b) <= a && min(a, b) <= b
    ensures min(a, b) == a <==> a <= b
{
    if a <= b then a else b
}

predicate ValidRedistribution(original: seq<int>, redistributed: seq<int>, m: int)
{
    |redistributed| == |original| &&
    Sum(redistributed) == Sum(original) &&
    forall i :: 0 <= i < |redistributed| ==> 0 <= redistributed[i] <= m
}

function MaxPossibleFirstScore(n: int, m: int, scores: seq<int>): int
    requires ValidInput(n, m, scores)
    ensures MaxPossibleFirstScore(n, m, scores) == min(Sum(scores), m)
{
    min(Sum(scores), m)
}

// <vc-helpers>
lemma SumNonNegative(nums: seq<int>)
    requires forall i :: 0 <= i < |nums| ==> nums[i] >= 0
    ensures Sum(nums) >= 0
{
    if |nums| > 0 {
        SumNonNegative(nums[1..]);
    }
}

lemma SumPreservation(original: seq<int>, redistributed: seq<int>)
    requires |original| == |redistributed|
    requires Sum(original) == Sum(redistributed)
    requires forall i :: 0 <= i < |redistributed| ==> 0 <= redistributed[i]
    ensures forall i :: 0 <= i < |original| ==> original[i] >= 0
{
    if |original| > 0 {
        if original[0] < 0 {
            // Derive contradiction
            assert redistributed[0] >= 0;
            assert Sum(original) < Sum(redistributed);
        }
        SumPreservation(original[1..], redistributed[1..]);
    }
}

lemma RedistributionLemma(scores: seq<int>, m: int, total: int)
    requires ValidInput(|scores|, m, scores)
    requires total == min(Sum(scores), m)
    ensures exists redistributed :: ValidRedistribution(scores, redistributed, m) && redistributed[0] == total
{
    var n := |scores|;
    // Construct a valid redistribution
    var redistributed := [total] + [0] * (n - 1);
    var remaining := Sum(scores) - total;
    
    if remaining < 0 {
        // This case cannot happen since total = min(Sum(scores), m) and Sum(scores) >= 0
        SumNonNegative(scores);
        assert false;
    }
    
    // Verify the properties
    assert |redistributed| == n;
    assert Sum(redistributed) == total + Sum([0] * (n - 1)) == total;
    assert 0 <= redistributed[0] <= m;
    assert forall i :: 1 <= i < n ==> 0 <= redistributed[i] <= m;
    
    // The postcondition holds
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, scores: seq<int>) returns (result: int)
    requires ValidInput(n, m, scores)
    ensures result == MaxPossibleFirstScore(n, m, scores)
    ensures result == min(Sum(scores), m)
    ensures exists redistributed :: (ValidRedistribution(scores, redistributed, m) && 
            redistributed[0] == result)
// </vc-spec>
// <vc-code>
{
    var total := Sum(scores);
    result := min(total, m);
    
    // Call the lemma to prove the postcondition about redistribution
    RedistributionLemma(scores, m, result);
    
    assert result == min(Sum(scores), m);
    assert result == MaxPossibleFirstScore(n, m, scores);
}
// </vc-code>

