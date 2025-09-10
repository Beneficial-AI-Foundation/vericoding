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
function findSmallestNonMultiple(scores: seq<int>): int
    requires exists smallestNonMultiple :: IsSmallestNonMultiple(scores, smallestNonMultiple)
    ensures IsSmallestNonMultiple(scores, findSmallestNonMultiple(scores))
    ensures findSmallestNonMultiple(scores) in scores
    ensures findSmallestNonMultiple(scores) % 10 != 0
{
    var smallest := 101; // Max score is 100, so 101 is a safe upper bound
    var k := 0;
    while k < |scores|
        invariant 0 <= k <= |scores|
        invariant forall j :: 0 <= j < k && scores[j] % 10 != 0 ==> smallest <= scores[j]
        invariant smallest == 101 || (smallest % 10 != 0 && smallest in scores[0..k])
    {
        if scores[k] % 10 != 0 {
            if scores[k] < smallest {
                smallest := scores[k];
            }
        }
        k := k + 1;
    }
    smallest // Return the found smallest non-multiple
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
    } else if AllMultiplesOf10(scores) {
        result := 0;
    } else {
        // We know from the postcondition of CorrectResult that if totalSum % 10 == 0
        // AND not AllMultiplesOf10(scores), then such a smallestNonMultiple must exist.
        // Thus, we can safely call findSmallestNonMultiple.

        // Proof that such an element exists for findSmallestNonMultiple
        // Since not AllMultiplesOf10(scores), there exists at least one score[k] such that scores[k] % 10 != 0.
        // Let S_NM be the set of all scores x such that x % 10 != 0. S_NM is non-empty.
        // Since scores are between 1 and 100, S_NM is a non-empty finite set of integers.
        // Therefore, S_NM must have a minimum element. Let this be 'm'.
        // By definition, 'm' is in scores, 'm' % 10 != 0, and for all x in scores with x % 10 != 0, m <= x.
        // This 'm' satisfies IsSmallestNonMultiple(scores, m), thus the precondition for findSmallestNonMultiple holds.
        var smallestNonMultiple := findSmallestNonMultiple(scores);
        result := totalSum - smallestNonMultiple;
    }
}
// </vc-code>

