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
lemma SumAssoc(a: seq<int>, b: seq<int>)
    ensures sum(a + b) == sum(a) + sum(b)
    decreases |a|
{
    if |a| == 0 {
    } else {
        calc {
            sum(a + b);
            == sum(([a[0]] + a[1..]) + b);
            == sum([a[0]] + (a[1..] + b));
// </vc-helpers>

// <vc-spec>
method solve(scores: seq<int>) returns (result: int)
    requires ValidInput(scores)
    ensures CorrectResult(scores, result)
// </vc-spec>
// <vc-code>
lemma SumAssoc(a: seq<int>, b: seq<int>)
    ensures sum(a + b) == sum(a) + sum(b)
    decreases |a|
{
    if |a| == 0 {
    } else {
        calc {
            sum(a + b);
            == sum(([a[0]] + a[1..]) + b);
            == sum([a[0]] + (a[1..] + b));
// </vc-code>

