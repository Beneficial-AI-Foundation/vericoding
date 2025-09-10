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

// </vc-helpers>

// <vc-spec>
method solve(scores: seq<int>) returns (result: int)
    requires ValidInput(scores)
    ensures CorrectResult(scores, result)
// </vc-spec>
// <vc-code>
{
  var total := sum(scores);
  if total % 10 != 0 {
    result := total;
  } else {
    var i := 0;
    var minNonMult := 101;
    while i < |scores|
      invariant 0 <= i <= |scores|
      invariant minNonMult == 101 || (minNonMult in scores && minNonMult % 10 != 0 && forall j :: 0 <= j < i && scores[j] % 10 != 0 ==> minNonMult <= scores[j])
    {
      if scores[i] % 10 != 0 && scores[i] < minNonMult {
        minNonMult := scores[i];
      }
      i := i + 1;
    }
    if minNonMult == 101 {
      result := 0;
    } else {
      result := total - minNonMult;
    }
  }
}
// </vc-code>

