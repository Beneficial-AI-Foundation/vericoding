predicate ValidInput(testCases: seq<seq<int>>) {
    forall i :: 0 <= i < |testCases| ==> 
        |testCases[i]| >= 1 && 
        forall j :: 0 <= j < |testCases[i]| ==> testCases[i][j] >= 1
}

predicate ValidResults(results: seq<string>) {
    forall i :: 0 <= i < |results| ==> 
        results[i] == "First" || results[i] == "Second"
}

function CountLeadingOnes(piles: seq<int>): nat
    requires forall j :: 0 <= j < |piles| ==> piles[j] >= 1
{
    if |piles| == 0 then 0
    else if piles[0] != 1 then 0
    else 1 + CountLeadingOnes(piles[1..])
}

predicate CorrectGameResult(piles: seq<int>, result: string)
    requires |piles| >= 1
    requires forall j :: 0 <= j < |piles| ==> piles[j] >= 1
    requires result == "First" || result == "Second"
{
    var onesCount := |set j | 0 <= j < |piles| && piles[j] == 1|;
    var allOnes := (onesCount == |piles|);
    var leadingOnes := CountLeadingOnes(piles);
    if allOnes then
        (if onesCount % 2 == 1 then result == "First" else result == "Second")
    else
        (if leadingOnes % 2 == 1 then result == "Second" else result == "First")
}

// <vc-helpers>
method Decide(piles: seq<int>) returns (r: string)
    requires |piles| >= 1
    requires forall j :: 0 <= j < |piles| ==> piles[j] >= 1
    ensures CorrectGameResult(piles, r)
{
  var onesCount := |set j | 0 <= j < |piles| && piles[j] == 1|;
  var allOnes := onesCount == |piles|;
  var leadingOnes: nat := 0;
  if allOnes {
    if onesCount % 2 == 1 {
      r := "First";
    } else {
      r := "Second";
    }
  } else {
    leadingOnes := CountLeadingOnes(piles);
    if leadingOnes % 2 == 1 {
      r := "Second";
    } else {
      r := "First";
    }
  }
  // r is one of the two expected values
  assert r == "First" || r == "Second";

  if allOnes {
    // In the all-ones case, correctness follows from onesCount
    assert (if onesCount % 2 == 1 then r == "First" else r == "Second");
    assert CorrectGameResult(piles, r);
  } else {
    // In the non-all-ones case, correctness follows from leadingOnes
    assert (if leadingOnes % 2 == 1 then r == "Second" else r == "First");
    assert CorrectGameResult(piles, r);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(testCases: seq<seq<int>>) returns (results: seq<string>)
    requires ValidInput(testCases)
    ensures |results| == |testCases|
    ensures ValidResults(results)
    ensures forall i :: 0 <= i < |testCases| ==> CorrectGameResult(testCases[i], results[i])
// </vc-spec>
// <vc-code>
{
  var res := [];
  var i := 0;
  while i < |testCases|
    invariant 0 <= i <= |testCases|
    invariant |res| == i
    invariant forall k :: 0 <= k < |res| ==> res[k] == "First" || res[k] == "Second"
    invariant forall k :: 0 <= k < |res| ==> CorrectGameResult(testCases[k], res[k])
    invariant ValidInput(testCases)
  {
    var r := Decide(testCases[i]);
    res := res + [r];
    i := i + 1;
  }
  results := res;
}
// </vc-code>

