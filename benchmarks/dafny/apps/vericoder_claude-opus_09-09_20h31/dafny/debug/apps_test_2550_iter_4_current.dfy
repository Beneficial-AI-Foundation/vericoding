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
    
    var remaining := total - target;
    assert remaining >= 0 by {
        assert target <= total;
    }
    
    if |scores| == 1 {
        var redistributed := [target];
        assert Sum(redistributed) == target == total;
        assert ValidRedistribution(scores, redistributed, m);
        assert redistributed[0] == target;
    } else {
        var positions := |scores| - 1;
        var left := remaining;
        var built := [target];
        var idx := 0;
        
        assert Sum(built) == target;
        assert Sum(built[1..]) == 0;
        
        while idx < positions && left > 0
            invariant 0 <= idx <= positions
            invariant |built| == idx + 1
            invariant built[0] == target
            invariant forall j :: 1 <= j < |built| ==> 0 <= built[j] <= m
            invariant left >= 0
            invariant Sum(built) == target + (remaining - left)
            invariant Sum(built[1..]) == remaining - left
        {
            var take := min(left, m);
            assert take >= 0 && take <= m;
            
            var old_sum := Sum(built);
            var old_tail_sum := Sum(built[1..]);
            
            built := built + [take];
            
            SumExtend(built[..|built|-1], take);
            assert Sum(built) == old_sum + take;
            assert Sum(built) == target + (remaining - left) + take;
            
            assert built[1..] == built[1..|built|-1] + [take];
            SumExtend(built[1..|built|-1], take);
            assert Sum(built[1..]) == old_tail_sum + take;
            assert Sum(built[1..]) == (remaining - left) + take;
            
            left := left - take;
            idx := idx + 1;
            
            assert Sum(built[1..]) == remaining - left;
            assert Sum(built) == target + (remaining - left);
        }
        
        assert left >= 0;
        assert Sum(built) == target + (remaining - left);
        
        while idx < positions
            invariant idx <= positions
            invariant |built| == idx + 1
            invariant built[0] == target
            invariant forall j :: 1 <= j < |built| ==> 0 <= built[j] <= m
            invariant Sum(built) == target + (remaining - left)
            invariant Sum(built[1..]) == remaining - left
        {
            var old_sum := Sum(built);
            var old_tail_sum := Sum(built[1..]);
            
            built := built + [0];
            
            SumExtend(built[..|built|-1], 0);
            assert Sum(built) == old_sum + 0;
            assert Sum(built) == target + (remaining - left);
            
            assert built[1..] == built[1..|built|-1] + [0];
            SumExtend(built[1..|built|-1], 0);
            assert Sum(built[1..]) == old_tail_sum + 0;
            assert Sum(built[1..]) == remaining - left;
            
            idx := idx + 1;
        }
        
        var redistributed := built;
        
        assert |redistributed| == |scores|;
        assert redistributed[0] == target;
        assert forall i :: 0 <= i < |redistributed| ==> 0 <= redistributed[i] <= m;
        assert Sum(redistributed) == target + (remaining - left);
        assert Sum(redistributed) == target + remaining - left;
        assert left == 0 || left > 0;
        
        if left == 0 {
            assert Sum(redistributed) == target + remaining;
            assert Sum(redistributed) == total;
        } else {
            // left > 0 means we filled all positions with m and still have leftover
            // This can only happen if remaining > m * positions
            assert idx == positions;
            assert left == remaining - Sum(built[1..]);
            // But this is impossible given our constraints
            assert false;
        }
        
        assert Sum(redistributed) == total;
        assert ValidRedistribution(scores, redistributed, m);
        assert redistributed[0] == target;
    }
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

