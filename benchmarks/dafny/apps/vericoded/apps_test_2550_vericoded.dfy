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
    } else {
        SumNonNegative(scores[1..]);
    }
}

function ConstructRedistribution(scores: seq<int>, m: int, firstScore: int): seq<int>
    requires |scores| >= 1
    requires firstScore >= 0
    requires Sum(scores) >= firstScore
{
    var remaining := Sum(scores) - firstScore;
    var n := |scores|;
    if n == 1 then [firstScore]
    else 
        var perStudent := remaining / (n - 1);
        var extra := remaining % (n - 1);
        [firstScore] + seq(n - 1, i => if i < extra then perStudent + 1 else perStudent)
}

lemma ConstructRedistributionValid(scores: seq<int>, m: int, firstScore: int)
    requires ValidInput(|scores|, m, scores)
    requires firstScore == min(Sum(scores), m)
    ensures var redistributed := ConstructRedistribution(scores, m, firstScore);
            ValidRedistribution(scores, redistributed, m) && redistributed[0] == firstScore
{
    var redistributed := ConstructRedistribution(scores, m, firstScore);
    var n := |scores|;
    var remaining := Sum(scores) - firstScore;
    
    SumNonNegative(scores);
    
    if n == 1 {
        assert redistributed == [firstScore];
        assert Sum(redistributed) == firstScore;
        assert Sum(scores) == scores[0];
        assert firstScore == min(scores[0], m);
        assert firstScore <= scores[0] && firstScore <= m;
    } else {
        var perStudent := remaining / (n - 1);
        var extra := remaining % (n - 1);
        
        assert remaining >= 0;
        assert perStudent >= 0;
        assert 0 <= extra < (n - 1);
        
        ConstructRedistributionSum(scores, m, firstScore);
        ConstructRedistributionBounds(scores, m, firstScore);
    }
}

lemma ConstructRedistributionSum(scores: seq<int>, m: int, firstScore: int)
    requires ValidInput(|scores|, m, scores)
    requires firstScore == min(Sum(scores), m)
    requires |scores| > 1
    ensures var redistributed := ConstructRedistribution(scores, m, firstScore);
            Sum(redistributed) == Sum(scores)
{
    var redistributed := ConstructRedistribution(scores, m, firstScore);
    var n := |scores|;
    var remaining := Sum(scores) - firstScore;
    var perStudent := remaining / (n - 1);
    var extra := remaining % (n - 1);
    var tail := redistributed[1..];
    
    calc {
        Sum(redistributed);
        firstScore + Sum(tail);
        { SumTailCalculation(tail, perStudent, extra, n - 1); }
        firstScore + (perStudent * (n - 1) + extra);
        firstScore + remaining;
        Sum(scores);
    }
}

lemma SumTailCalculation(tail: seq<int>, perStudent: int, extra: int, len: int)
    requires |tail| == len
    requires len > 0
    requires forall i :: 0 <= i < |tail| ==> tail[i] == (if i < extra then perStudent + 1 else perStudent)
    requires 0 <= extra <= len
    ensures Sum(tail) == len * perStudent + extra
    decreases len
{
    if len == 1 {
        if extra > 0 {
            assert tail[0] == perStudent + 1;
            assert Sum(tail) == perStudent + 1;
            assert len * perStudent + extra == 1 * perStudent + extra == perStudent + extra;
        } else {
            assert tail[0] == perStudent;
            assert Sum(tail) == perStudent;
            assert len * perStudent + extra == 1 * perStudent + 0 == perStudent;
        }
    } else {
        var subTail := tail[1..];
        var newExtra := if extra > 0 then extra - 1 else 0;
        assert |subTail| == len - 1;
        
        if extra > 0 {
            assert tail[0] == perStudent + 1;
            assert forall i :: 0 <= i < |subTail| ==> subTail[i] == (if i < newExtra then perStudent + 1 else perStudent);
            SumTailCalculation(subTail, perStudent, newExtra, len - 1);
            assert Sum(subTail) == (len - 1) * perStudent + newExtra;
            assert Sum(tail) == tail[0] + Sum(subTail);
            assert Sum(tail) == (perStudent + 1) + ((len - 1) * perStudent + (extra - 1));
            assert Sum(tail) == len * perStudent + extra;
        } else {
            assert tail[0] == perStudent;
            assert forall i :: 0 <= i < |subTail| ==> subTail[i] == perStudent;
            SumTailCalculation(subTail, perStudent, newExtra, len - 1);
            assert Sum(subTail) == (len - 1) * perStudent;
            assert Sum(tail) == tail[0] + Sum(subTail);
            assert Sum(tail) == perStudent + (len - 1) * perStudent;
            assert Sum(tail) == len * perStudent;
        }
    }
}

lemma ConstructRedistributionBounds(scores: seq<int>, m: int, firstScore: int)
    requires ValidInput(|scores|, m, scores)
    requires firstScore == min(Sum(scores), m)
    requires |scores| > 1
    ensures var redistributed := ConstructRedistribution(scores, m, firstScore);
            forall i :: 0 <= i < |redistributed| ==> 0 <= redistributed[i] <= m
{
    var redistributed := ConstructRedistribution(scores, m, firstScore);
    var n := |scores|;
    var remaining := Sum(scores) - firstScore;
    var perStudent := remaining / (n - 1);
    var extra := remaining % (n - 1);
    
    SumNonNegative(scores);
    assert firstScore <= m;
    assert 0 <= redistributed[0] <= m;
    
    assert remaining >= 0;
    assert perStudent >= 0;
    
    SumUpperBound(scores, m);
    assert Sum(scores) <= n * m;
    
    if firstScore == m {
        assert remaining == Sum(scores) - m;
        assert remaining <= n * m - m == (n - 1) * m;
        assert perStudent <= m;
        assert perStudent + 1 <= m + 1;
        
        if perStudent + 1 <= m {
            assert forall i :: 1 <= i < n ==> 0 <= redistributed[i] <= m;
        } else {
            assert perStudent + 1 == m + 1;
            assert perStudent == m;
            assert remaining == (n - 1) * m;
            assert Sum(scores) == m + (n - 1) * m == n * m;
            
            SumUpperBoundTight(scores, m);
            assert extra == 0;
            assert forall i :: 1 <= i < n ==> redistributed[i] == perStudent == m;
            assert forall i :: 1 <= i < n ==> 0 <= redistributed[i] <= m;
        }
    } else {
        assert firstScore < m;
        assert Sum(scores) < m;
        assert remaining < m;
        assert perStudent < m;
        assert perStudent + 1 <= m;
        assert forall i :: 1 <= i < n ==> 0 <= redistributed[i] <= m;
    }
}

lemma SumUpperBound(scores: seq<int>, m: int)
    requires forall i :: 0 <= i < |scores| ==> 0 <= scores[i] <= m
    ensures Sum(scores) <= |scores| * m
{
    if |scores| == 0 {
    } else {
        SumUpperBound(scores[1..], m);
        assert Sum(scores[1..]) <= |scores[1..]| * m;
        assert Sum(scores) == scores[0] + Sum(scores[1..]);
        assert Sum(scores) <= m + |scores[1..]| * m;
        assert Sum(scores) <= |scores| * m;
    }
}

lemma SumUpperBoundTight(scores: seq<int>, m: int)
    requires forall i :: 0 <= i < |scores| ==> 0 <= scores[i] <= m
    requires Sum(scores) == |scores| * m
    ensures forall i :: 0 <= i < |scores| ==> scores[i] == m
{
    if |scores| == 0 {
    } else {
        assert Sum(scores) == scores[0] + Sum(scores[1..]);
        assert scores[0] + Sum(scores[1..]) == |scores| * m;
        assert scores[0] + Sum(scores[1..]) == m + |scores[1..]| * m;
        
        SumUpperBound(scores[1..], m);
        assert Sum(scores[1..]) <= |scores[1..]| * m;
        
        assert scores[0] <= m;
        assert scores[0] + Sum(scores[1..]) <= m + |scores[1..]| * m;
        assert scores[0] + Sum(scores[1..]) == m + |scores[1..]| * m;
        
        assert Sum(scores[1..]) >= |scores[1..]| * m;
        assert Sum(scores[1..]) <= |scores[1..]| * m;
        assert Sum(scores[1..]) == |scores[1..]| * m;
        assert scores[0] == m;
        
        if |scores[1..]| > 0 {
            SumUpperBoundTight(scores[1..], m);
        }
        assert forall i :: 0 <= i < |scores[1..]| ==> scores[1..][i] == m;
        assert forall i :: 1 <= i < |scores| ==> scores[i] == m;
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
    SumNonNegative(scores);
    result := min(Sum(scores), m);
    ConstructRedistributionValid(scores, m, result);
    var redistributed := ConstructRedistribution(scores, m, result);
    assert ValidRedistribution(scores, redistributed, m) && redistributed[0] == result;
}
// </vc-code>

