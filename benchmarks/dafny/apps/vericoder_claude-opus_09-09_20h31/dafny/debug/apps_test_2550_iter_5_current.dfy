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

lemma SumAppend(a: seq<int>, b: seq<int>)
    ensures Sum(a + b) == Sum(a) + Sum(b)
{
    if |a| == 0 {
        assert a + b == b;
    } else {
        assert (a + b)[0] == a[0];
        assert (a + b)[1..] == a[1..] + b;
        SumAppend(a[1..], b);
    }
}

lemma SumSingleton(x: int)
    ensures Sum([x]) == x
{
    assert [x][0] == x;
    assert [x][1..] == [];
}

lemma SumExtend(s: seq<int>, x: int)
    ensures Sum(s + [x]) == Sum(s) + x
{
    if |s| == 0 {
        assert s + [x] == [x];
        SumSingleton(x);
    } else {
        assert (s + [x])[0] == s[0];
        assert (s + [x])[1..] == s[1..] + [x];
        SumExtend(s[1..], x);
    }
}

lemma ConstructRedistribution(n: int, m: int, scores: seq<int>, target: int)
    requires ValidInput(n, m, scores)
    requires target == min(Sum(scores), m)
    ensures exists redistributed :: ValidRedistribution(scores, redistributed, m) && redistributed[0] == target
{
    var total := Sum(scores);
    SumNonNegative(scores);
    
    if target == m {
        // target is m, which means Sum(scores) >= m
        assert total >= m;
        
        // Create a redistribution where first position gets m and rest get appropriate values
        var redistributed := [m] + scores[1..];
        assert |redistributed| == |scores|;
        assert redistributed[0] == m == target;
        
        // The sum is preserved since we're using the original tail
        assert Sum(redistributed) == m + Sum(scores[1..]);
        assert Sum(scores) == scores[0] + Sum(scores[1..]);
        
        // We need to show Sum(redistributed) == Sum(scores)
        // This requires redistributing from scores[0] to make up the difference
        // But we need a proper redistribution
        
        // Actually construct it properly
        var remaining := total - m;
        assert remaining >= 0;
        
        if |scores| == 1 {
            var red := [m];
            assert Sum(red) == m;
            assert m == total; // Since target == m and target == min(total, m), and |scores| == 1
            assert ValidRedistribution(scores, red, m);
        } else {
            // Build redistribution by filling positions with appropriate amounts
            var built := BuildRedistribution(scores, m, remaining);
            assert |built| == |scores|;
            assert built[0] == m;
            assert Sum(built) == total;
            assert ValidRedistribution(scores, built, m);
        }
    } else {
        // target < m, which means target == Sum(scores)
        assert target == total;
        assert total <= m;
        
        // All points go to first position, rest get 0
        var redistributed := [total];
        var idx := 1;
        while idx < |scores|
            invariant 1 <= idx <= |scores|
            invariant |redistributed| == idx
            invariant redistributed[0] == total
            invariant forall j :: 1 <= j < |redistributed| ==> redistributed[j] == 0
            invariant Sum(redistributed) == total
        {
            redistributed := redistributed + [0];
            SumExtend(redistributed[..|redistributed|-1], 0);
            idx := idx + 1;
        }
        
        assert |redistributed| == |scores|;
        assert redistributed[0] == total == target;
        assert Sum(redistributed) == total;
        assert ValidRedistribution(scores, redistributed, m);
    }
}

function BuildRedistribution(scores: seq<int>, firstAmount: int, remaining: int): seq<int>
    requires |scores| >= 2
    requires 0 <= firstAmount <= Sum(scores)
    requires remaining == Sum(scores) - firstAmount
    requires remaining >= 0
    ensures |BuildRedistribution(scores, firstAmount, remaining)| == |scores|
    ensures BuildRedistribution(scores, firstAmount, remaining)[0] == firstAmount
    ensures Sum(BuildRedistribution(scores, firstAmount, remaining)) == Sum(scores)
{
    if |scores| == 2 then
        [firstAmount, remaining]
    else
        var take := min(remaining, firstAmount); // Use same max as first position for simplicity
        [firstAmount] + BuildRedistribution(scores[1..], take, remaining - take)
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

