predicate ValidInput(scores: seq<int>) {
    |scores| > 0 && |scores| <= 100 &&
    forall i :: 0 <= i < |scores| ==> 1 <= scores[i] <= 100
}

function sum(scores: seq<int>): int {
    if |scores| == 0 then 0
    else scores[0] + sum(scores[1..])
}

predicate AllMultiplesOf10(scores: seq<int>) {
    forall i :: 0 <= i < |scores| ==> scores[i] % 10 == 0
}

predicate IsSmallestNonMultiple(scores: seq<int>, value: int) {
    value in scores && 
    value % 10 != 0 &&
    forall x :: x in scores && x % 10 != 0 ==> value <= x
}

predicate CorrectResult(scores: seq<int>, result: int) {
    var totalSum := sum(scores);
    if totalSum % 10 != 0 then
        result == totalSum
    else if AllMultiplesOf10(scores) then
        result == 0
    else
        exists smallestNonMultiple :: 
            IsSmallestNonMultiple(scores, smallestNonMultiple) &&
            result == totalSum - smallestNonMultiple
}

// <vc-helpers>
lemma SumCorrect(scores: seq<int>)
    ensures sum(scores) == if |scores| == 0 then 0 else scores[0] + sum(scores[1..])
{
}

lemma SumBounds(scores: seq<int>)
    requires ValidInput(scores)
    ensures 1 <= sum(scores) <= 10000
{
    if |scores| == 1 {
        assert sum(scores) == scores[0];
        assert 1 <= scores[0] <= 100;
    } else {
        assert scores == [scores[0]] + scores[1..];
        assert ValidInput(scores[1..]);
        SumBounds(scores[1..]);
    }
}

method ComputeSum(scores: seq<int>) returns (total: int)
    requires ValidInput(scores)
    ensures total == sum(scores)
{
    total := 0;
    var i := 0;
    
    while i < |scores|
        invariant 0 <= i <= |scores|
        invariant total == sum(scores[..i])
    {
        total := total + scores[i];
        assert scores[..i+1] == scores[..i] + [scores[i]];
        i := i + 1;
    }
    assert scores[..|scores|] == scores;
}

method FindSmallestNonMultiple(scores: seq<int>) returns (smallest: int, found: bool)
    requires ValidInput(scores)
    ensures found ==> IsSmallestNonMultiple(scores, smallest)
    ensures !found ==> AllMultiplesOf10(scores)
{
    smallest := 101;  // Start with value larger than any valid score
    found := false;
    
    var i := 0;
    while i < |scores|
        invariant 0 <= i <= |scores|
        invariant found ==> smallest in scores[..i] && smallest % 10 != 0
        invariant found ==> forall x :: x in scores[..i] && x % 10 != 0 ==> smallest <= x
        invariant !found ==> forall x :: x in scores[..i] ==> x % 10 == 0
        invariant !found ==> smallest == 101
        invariant found ==> 1 <= smallest <= 100
    {
        if scores[i] % 10 != 0 {
            if !found || scores[i] < smallest {
                smallest := scores[i];
                found := true;
            }
        }
        i := i + 1;
    }
    
    assert scores[..|scores|] == scores;
}
// </vc-helpers>

// <vc-spec>
method solve(scores: seq<int>) returns (result: int)
    requires ValidInput(scores)
    ensures CorrectResult(scores, result)
// </vc-spec>
// <vc-code>
{
    var totalSum := ComputeSum(scores);
    
    if totalSum % 10 != 0 {
        result := totalSum;
    } else {
        var smallest, found := FindSmallestNonMultiple(scores);
        
        if found {
            result := totalSum - smallest;
            assert IsSmallestNonMultiple(scores, smallest);
            assert !AllMultiplesOf10(scores);
        } else {
            result := 0;
            assert AllMultiplesOf10(scores);
        }
    }
}
// </vc-code>

