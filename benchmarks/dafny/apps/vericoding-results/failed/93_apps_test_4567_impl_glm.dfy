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
lemma AllMultiplesOf10ImpliesAllElementsMultiplesOf10(scores: seq<int>)
    requires AllMultiplesOf10(scores)
    ensures forall i :: 0 <= i < |scores| ==> scores[i] % 10 == 0
{
}

method SmallestNonMultipleExists(scores: seq<int>) returns (smallest: int)
    requires !AllMultiplesOf10(scores)
    ensures smallest in scores
    ensures smallest % 10 != 0
    ensures forall x :: x in scores && x % 10 != 0 ==> smallest <= x
{
    var firstNonMultipleIndex := 0;
    while firstNonMultipleIndex < |scores| && scores[firstNonMultipleIndex] % 10 == 0
        invariant 0 <= firstNonMultipleIndex <= |scores|
        invariant forall j :: 0 <= j < firstNonMultipleIndex ==> scores[j] % 10 == 0
    {
        firstNonMultipleIndex := firstNonMultipleIndex + 1;
    }
    assert firstNonMultipleIndex < |scores|;
    smallest := scores[firstNonMultipleIndex];
    assert smallest in scores;
    assert smallest % 10 != 0;
    
    var i := firstNonMultipleIndex + 1;
    while i < |scores|
        invariant firstNonMultipleIndex < i <= |scores|
        invariant smallest in scores
        invariant smallest % 10 != 0
        invariant forall x :: x in scores[0..i] && x % 10 != 0 ==> smallest <= x
    {
        if scores[i] % 10 != 0 && scores[i] < smallest {
            smallest := scores[i];
        }
        i := i + 1;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(scores: seq<int>) returns (result: int)
    requires ValidInput(scores)
    ensures CorrectResult(scores, result)
// </vc-spec>
// <vc-code>
{
    var totalSum := sum(scores);
    if (totalSum % 10 != 0) {
        return totalSum;
    } else {
        if (AllMultiplesOf10(scores)) {
            return 0;
        } else {
            var smallest := SmallestNonMultipleExists(scores);
            return totalSum - smallest;
        }
    }
}
// </vc-code>

