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

lemma SumZeros(n: nat)
    ensures Sum(seq(n, i => 0)) == 0
{
    if n == 0 {
        assert seq(0, i => 0) == [];
    } else {
        var s := seq(n, i => 0);
        assert s[0] == 0;
        assert s[1..] == seq(n-1, i => 0);
        SumZeros(n-1);
    }
}

lemma ConstructRedistribution(n: int, m: int, scores: seq<int>, target: int)
    requires ValidInput(n, m, scores)
    requires target == min(Sum(scores), m)
    ensures exists redistributed :: ValidRedistribution(scores, redistributed, m) && redistributed[0] == target
{
    var total := Sum(scores);
    SumNonNegative(scores);
    
    var remaining := total - target;
    assert remaining >= 0 by {
        assert target <= total;
    }
    
    // Distribute remaining across other positions, respecting the max value m
    var redistributed: seq<int>;
    
    if |scores| == 1 {
        redistributed := [target];
        assert Sum(redistributed) == target == total;
    } else {
        // Distribute remaining values across positions 1 to n-1, each getting at most m
        var positions := |scores| - 1;
        redistributed := [target];
        var left := remaining;
        
        // Build the rest of the sequence by distributing `left` across remaining positions
        var rest := seq(positions, i => if i < positions - 1 then min(left - min(left, m) * i, m) else left - min(left, m) * (positions - 1));
        
        // Simple approach: fill positions with up to m until we run out
        var idx := 0;
        var built := [target];
        while idx < positions && left > 0
            invariant 0 <= idx <= positions
            invariant |built| == idx + 1
            invariant built[0] == target
            invariant forall j :: 0 < j < |built| ==> 0 <= built[j] <= m
            invariant Sum(built[1..]) == remaining - left
        {
            var take := min(left, m);
            built := built + [take];
            left := left - take;
            idx := idx + 1;
        }
        
        // Fill remaining positions with 0
        while idx < positions
            invariant positions - idx >= 0
            invariant |built| == idx + 1
            invariant built[0] == target
            invariant forall j :: 0 < j < |built| ==> 0 <= built[j] <= m
            invariant left == 0
        {
            built := built + [0];
            idx := idx + 1;
        }
        
        redistributed := built;
        
        // Verify the sum
        assert |redistributed| == |scores|;
        assert redistributed[0] == target;
        assert forall i :: 0 <= i < |redistributed| ==> 0 <= redistributed[i] <= m;
        
        // The sum should be correct
        assert Sum(redistributed) == total;
    }
    
    assert |redistributed| == |scores|;
    assert Sum(redistributed) == total;
    assert forall i :: 0 <= i < |redistributed| ==> 0 <= redistributed[i] <= m;
    assert ValidRedistribution(scores, redistributed, m);
    assert redistributed[0] == target;
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

