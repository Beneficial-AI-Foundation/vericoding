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
lemma RemoveSmallestNonMultipleMaintainsRest(scores: seq<int>, smallestNonMultiple: int)
  requires |scores| > 0
  requires IsSmallestNonMultiple(scores, smallestNonMultiple)
  ensures exists i :: 0 <= i < |scores| && scores[i] == smallestNonMultiple
  ensures forall x :: x in scores[..] && x % 10 != 0 ==> x == smallestNonMultiple || x > smallestNonMultiple
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
  var total := sum(scores);
  
  if total % 10 != 0 {
    result := total;
  } else if AllMultiplesOf10(scores) {
    result := 0;
  } else {
    // Find the smallest non-multiple of 10
    var smallestNonMultiple := 101; // Larger than any possible score
    var found := false;
    
    var i := 0;
    while i < |scores|
      invariant 0 <= i <= |scores|
      invariant !found ==> smallestNonMultiple == 101
      invariant found ==> smallestNonMultiple % 10 != 0 && smallestNonMultiple in scores[..i]
      invariant found ==> forall j :: 0 <= j < i && scores[j] % 10 != 0 ==> smallestNonMultiple <= scores[j]
    {
      if scores[i] % 10 != 0 && (!found || scores[i] < smallestNonMultiple) {
        smallestNonMultiple := scores[i];
        found := true;
      }
      i := i + 1;
    }
    
    assert found;
    result := total - smallestNonMultiple;
  }
}
// </vc-code>

