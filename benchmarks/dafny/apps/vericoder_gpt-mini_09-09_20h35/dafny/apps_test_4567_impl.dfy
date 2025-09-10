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
lemma SumPrefixCompatible(scores: seq<int>, i: int)
  requires 0 <= i <= |scores|
  ensures sum(scores) == sum(scores[..i]) + sum(scores[i..])
{
  if |scores| == 0 {
    // i == 0
    calc {
      sum(scores);
      == { }
      0;
      == { }
      sum(scores[..0]) + sum(scores[0..]);
    }
  } else {
    if i == 0 {
      // sum(scores[..0]) == 0 and sum(scores[0..]) == sum(scores)
      calc {
        sum(scores);
        == { }
        0 + sum(scores);
        == { }
        sum(scores[..0]) + sum(scores[0..]);
      }
    } else if i == |scores| {
      // sum(scores[..|scores|]) == sum(scores) and sum(scores[|scores|..]) == 0
      calc {
        sum(scores);
        == { }
        sum(scores) + 0;
        == { }
        sum(scores[..i]) + sum(scores[i..]);
      }
    } else {
      // 0 < i < |scores|
      SumPrefixCompatible(scores[1..], i - 1);
      calc {
        sum(scores);
        == { }
        scores[0] + sum(scores[1..]);
        == { SumPrefixCompatible(scores[1..], i - 1) }
        scores[0] + (sum(scores[1..i]) + sum(scores[i..]));
        == { }
        (scores[0] + sum(scores[1..i])) + sum(scores[i..]);
        == { }
        sum(scores[..i]) + sum(scores[i..]);
      }
    }
  }
}

lemma SumPrefixAdd(scores: seq<int>, i: int)
  requires 0 <= i < |scores|
  ensures sum(scores[..i+1]) == sum(scores[..i]) + scores[i]
{
  if i == 0 {
    calc {
      sum(scores[..1]);
      == { }
      scores[0];
      == { }
      0 + scores[0];
      == { }
      sum(scores[..0]) + scores[0];
    }
  } else {
    // reduce to the tail
    SumPrefixAdd(scores[1..], i - 1);
    calc {
      sum(scores[..i+1]);
      == { }
      scores[0] + sum(scores[1..i+1]);
      == { SumPrefixAdd(scores[1..], i - 1) }
      scores[0] + (sum(scores[1..i]) + scores[i]);
      == { }
      (scores[0] + sum(scores[1..i])) + scores[i];
      == { }
      sum(scores[..i]) + scores[i];
    }
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
  var total := 0;
  var i := 0;
  var minNon := 101;
  var found := false;
  while i < |scores|
    invariant 0 <= i <= |scores|
    invariant total == sum(scores[..i])
    invariant found == (exists j :: 0 <= j < i && scores[j] % 10 != 0)
    invariant if found then minNon in scores[..i] && minNon % 10 != 0 && (forall j :: 0 <= j < i && scores[j] % 10 != 0 ==> minNon <= scores[j]) else minNon == 101
  {
    var v := scores[i];
    total := total + v;
    SumPrefixAdd(scores, i);
    // relate updated total to the new prefix sum
    assert total == sum(scores[..i+1]);

    if v % 10 != 0 {
      if !found {
        minNon := v;
        found := true;
      } else if v < minNon {
        minNon := v;
      }
    }
    i := i + 1;
  }

  // At loop exit i == |scores|
  assert i == |scores|;
  // Relate total to sum(scores)
  SumPrefixCompatible(scores, |scores|);
  assert total == sum(scores[..i]);
  assert sum(scores) == sum(scores[..i]) + sum(scores[i..]);
  assert sum(scores[i..]) == 0;
  assert sum(scores) == total;

  if total % 10 != 0 {
    result := total;
    return;
  }
  if !found {
    // No non-multiples found implies all are multiples of 10
    assert forall j :: 0 <= j < |scores| ==> scores[j] % 10 == 0;
    result := 0;
    return;
  }

  // minNon is the smallest non-multiple by the invariant
  assert minNon in scores;
  assert minNon % 10 != 0;
  assert forall x :: x in scores && x % 10 != 0 ==> minNon <= x;

  result := total - minNon;
  // produce the existential witness required by the postcondition
  assert IsSmallestNonMultiple(scores, minNon);
  assert exists smallestNonMultiple :: IsSmallestNonMultiple(scores, smallestNonMultiple) && result == total - smallestNonMultiple;
  return;
}
// </vc-code>

