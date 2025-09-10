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
lemma SumPreservation(scores: seq<int>)
    ensures sum(scores) == if |scores| == 0 then 0 else scores[0] + sum(scores[1..])
{
}

function findSmallestNonMultiple(scores: seq<int>): int
    requires |scores| > 0
    requires exists i :: 0 <= i < |scores| && scores[i] % 10 != 0
    ensures findSmallestNonMultiple(scores) in scores
    ensures findSmallestNonMultiple(scores) % 10 != 0
    ensures forall x :: x in scores && x % 10 != 0 ==> findSmallestNonMultiple(scores) <= x
{
    var nonMultiples := seq(i | 0 <= i < |scores| && scores[i] % 10 != 0 :: i);
    var nonMultipleValues := seq(i | 0 <= i < |nonMultiples| :: scores[nonMultiples[i]]);
    assert |nonMultipleValues| > 0;
    minSeq(nonMultipleValues)
}

function minSeq(s: seq<int>): int
    requires |s| > 0
    ensures minSeq(s) in s
    ensures forall x :: x in s ==> minSeq(s) <= x
{
    if |s| == 1 then s[0]
    else if s[0] <= minSeq(s[1..]) then s[0]
    else minSeq(s[1..])
}

lemma MinSeqCorrect(s: seq<int>)
    requires |s| > 0
    ensures minSeq(s) in s
    ensures forall x :: x in s ==> minSeq(s) <= x
{
}

lemma FindSmallestCorrect(scores: seq<int>)
    requires |scores| > 0
    requires exists i :: 0 <= i < |scores| && scores[i] % 10 != 0
    ensures IsSmallestNonMultiple(scores, findSmallestNonMultiple(scores))
{
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
    
    if totalSum % 10 != 0 {
        result := totalSum;
    } else {
        var hasNonMultiple := exists i :: 0 <= i < |scores| && scores[i] % 10 != 0;
        
        if !hasNonMultiple {
            result := 0;
            assert AllMultiplesOf10(scores);
        } else {
            var smallest := findSmallestNonMultiple(scores);
            FindSmallestCorrect(scores);
            assert IsSmallestNonMultiple(scores, smallest);
            result := totalSum - smallest;
        }
    }
}
// </vc-code>

