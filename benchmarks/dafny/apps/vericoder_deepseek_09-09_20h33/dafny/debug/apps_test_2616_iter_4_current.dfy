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
lemma CountLeadingOnesNonNegative(piles: seq<int>)
    requires forall j :: 0 <= j < |piles| ==> piles[j] >= 1
    ensures CountLeadingOnes(piles) >= 0
{
}

lemma LeadingOnesLessEqualLength(piles: seq<int>)
    requires forall j :: 0 <= j < |piles| ==> piles[j] >= 1
    ensures CountLeadingOnes(piles) <= |piles|
{
}

lemma CountOnesInSet(piles: seq<int>)
    requires |piles| >= 1 && forall j :: 0 <= j < |piles| ==> piles[j] >= 1
    ensures |set j | 0 <= j < |piles| && piles[j] == 1| >= 0
{
}

lemma AllOnesImpliesCorrectGameResult(piles: seq<int>, result: string)
    requires |piles| >= 1 && forall j :: 0 <= j < |piles| ==> piles[j] >= 1
    requires result == "First" || result == "Second"
    requires |set j | 0 <= j < |piles| && piles[j] == 1| == |piles|
    ensures CorrectGameResult(piles, result) == 
        (if |piles| % 2 == 1 then result == "First" else result == "Second")
{
}

lemma NonAllOnesImpliesCorrectGameResult(piles: seq<int>, result: string)
    requires |piles| >= 1 && forall j :: 0 <= j < |piles| ==> piles[j] >= 1
    requires result == "First" || result == "Second"
    requires |set j | 0 <= j < |piles| && piles[j] == 1| != |piles|
    ensures CorrectGameResult(piles, result) == 
        (if CountLeadingOnes(piles) % 2 == 1 then result == "Second" else result == "First")
{
}

lemma CountLeadingOnesEqualsSetCount(piles: seq<int>)
    requires forall j :: 0 <= j < |piles| ==> piles[j] >= 1
    ensures CountLeadingOnes(piles) == |set j | 0 <= j < CountLeadingOnes(piles) && piles[j] == 1|
{
    if |piles| == 0 {
    } else if piles[0] != 1 {
    } else {
        var sub := piles[1..];
        CountLeadingOnesEqualsSetCount(sub);
    }
}

lemma CountLeadingOnesIsExact(piles: seq<int>)
    requires forall j :: 0 <= j < |piles| ==> piles[j] >= 1
    ensures CountLeadingOnes(piles) == 
        (if |piles| > 0 && piles[0] == 1 then 1 + CountLeadingOnes(piles[1..]) else 0)
{
}

lemma CountLeadingOnesMaintainsInvariant(piles: seq<int>, n: nat)
    requires forall j :: 0 <= j < |piles| ==> piles[j] >= 1
    requires n <= |piles|
    requires forall j :: 0 <= j < n ==> piles[j] == 1
    requires n == CountLeadingOnes(piles[0..n])
    ensures n == CountLeadingOnes(piles)
    decreases |piles| - n
{
    if n < |piles| && piles[n] == 1 {
        CountLeadingOnesMaintainsInvariant(piles, n+1);
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
    results := [];
    var i := 0;
    while i < |testCases|
        invariant 0 <= i <= |testCases|
        invariant |results| == i
        invariant ValidResults(results)
        invariant forall j :: 0 <= j < i ==> CorrectGameResult(testCases[j], results[j])
    {
        var piles := testCases[i];
        var onesCount := 0;
        while onesCount < |piles| && piles[onesCount] == 1
            invariant 0 <= onesCount <= |piles|
            invariant forall j :: 0 <= j < onesCount ==> piles[j] == 1
            invariant onesCount == CountLeadingOnes(piles[0..onesCount])
        {
            onesCount := onesCount + 1;
        }
        CountLeadingOnesMaintainsInvariant(piles, onesCount);
        
        var allOnes := onesCount == |piles|;
        var result: string;
        if allOnes {
            result := if |piles| % 2 == 1 then "First" else "Second";
        } else {
            result := if onesCount % 2 == 1 then "Second" else "First";
        }
        results := results + [result];
        i := i + 1;
    }
}
// </vc-code>

