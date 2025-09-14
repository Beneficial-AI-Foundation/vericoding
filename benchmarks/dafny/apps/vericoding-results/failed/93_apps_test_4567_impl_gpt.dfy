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
  var totalSum := sum(scores);
  if totalSum % 10 != 0 {
    result := totalSum;
    return;
  }

  var n := |scores|;
  var i := 0;
  var found := false;
  var min := 0;

  while i < n
    invariant 0 <= i <= n
    invariant n == |scores|
    invariant (!found ==> forall j :: 0 <= j < i ==> scores[j] % 10 == 0)
    invariant (found ==> min % 10 != 0)
    invariant (found ==> min in scores[0..i])
    invariant (found ==> forall x :: x in scores[0..i] && x % 10 != 0 ==> min <= x)
    decreases n - i
  {
    var x := scores[i];
    if x % 10 != 0 {
      if !found {
        found := true;
        min := x;
      } else if x < min {
        min := x;
      }
    }
    i := i + 1;
  }

  assert i == n;

  if !found {
    assert forall j :: 0 <= j < |scores| ==> scores[j] % 10 == 0;
    assert AllMultiplesOf10(scores);
    result := 0;
  } else {
    assert n == |scores|;
    assert i == |scores|;
    assert scores[0..i] == scores;
    assert min in scores;
    assert min % 10 != 0;
    assert forall x :: x in scores && x % 10 != 0 ==> min <= x;
    assert IsSmallestNonMultiple(scores, min);
    result := totalSum - min;
  }
}
// </vc-code>

