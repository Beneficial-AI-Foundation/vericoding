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
lemma SumNonNegative(scores: seq<int>)
    requires forall i :: 0 <= i < |scores| ==> scores[i] >= 0
    ensures Sum(scores) >= 0
{
    if |scores| == 0 {
        // Base case: empty sequence has sum 0
    } else {
        // Inductive case
        assert scores[0] >= 0;
        SumNonNegative(scores[1..]);
        assert Sum(scores) == scores[0] + Sum(scores[1..]);
    }
}

lemma ConstructRedistribution(n: int, m: int, scores: seq<int>, target: int)
    requires ValidInput(n, m, scores)
    requires target == min(Sum(scores), m)
    ensures exists redistributed :: ValidRedistribution(scores, redistributed, m) && redistributed[0] == target
{
    var total := Sum(scores);
    
    // Construct the redistribution
    var redistributed := [target] + seq(|scores| - 1, i => 0);
    
    // Need to distribute the remaining sum
    var remaining := total - target;
    assert remaining >= 0 by {
        if target == total {
            assert remaining == 0;
        } else {
            assert target == m;
            assert total > m;
            assert remaining == total - m > 0;
        }
    }
    
    // Simple redistribution: put all remaining in position 1 if n > 1, otherwise we're done
    if |scores| == 1 {
        assert target == total;
        redistributed := [target];
    } else {
        redistributed := [target, remaining] + seq(|scores| - 2, i => 0);
    }
    
    assert |redistributed| == |scores|;
    assert Sum(redistributed) == total by {
        if |scores| == 1 {
            assert redistributed == [target];
            assert Sum(redistributed) == target == total;
        } else {
            assert redistributed[0] == target;
            assert redistributed[1] == remaining;
            // The sum is target + remaining + 0s = total
        }
    }
    
    assert ValidRedistribution(scores, redistributed, m) && redistributed[0] == target;
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
    SumNonNegative(scores);
    
    result := if total <= m then total else m;
    
    assert result == min(total, m);
    assert result == min(Sum(scores), m);
    assert result == MaxPossibleFirstScore(n, m, scores);
    
    ConstructRedistribution(n, m, scores, result);
}
// </vc-code>

