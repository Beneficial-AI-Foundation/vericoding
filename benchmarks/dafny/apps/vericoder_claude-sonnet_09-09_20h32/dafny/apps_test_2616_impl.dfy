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
lemma CountLeadingOnesCorrect(piles: seq<int>)
    requires forall j :: 0 <= j < |piles| ==> piles[j] >= 1
    ensures CountLeadingOnes(piles) <= |piles|
{
    if |piles| == 0 {
    } else if piles[0] != 1 {
    } else {
        CountLeadingOnesCorrect(piles[1..]);
    }
}

function ComputeResult(piles: seq<int>): string
    requires |piles| >= 1
    requires forall j :: 0 <= j < |piles| ==> piles[j] >= 1
    ensures ComputeResult(piles) == "First" || ComputeResult(piles) == "Second"
    ensures CorrectGameResult(piles, ComputeResult(piles))
{
    var onesCount := |set j | 0 <= j < |piles| && piles[j] == 1|;
    var allOnes := (onesCount == |piles|);
    var leadingOnes := CountLeadingOnes(piles);
    
    if allOnes then
        (if onesCount % 2 == 1 then "First" else "Second")
    else
        (if leadingOnes % 2 == 1 then "Second" else "First")
}

lemma ComputeResultCorrect(piles: seq<int>)
    requires |piles| >= 1
    requires forall j :: 0 <= j < |piles| ==> piles[j] >= 1
    ensures CorrectGameResult(piles, ComputeResult(piles))
{
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
        invariant forall k :: 0 <= k < i ==> CorrectGameResult(testCases[k], results[k])
    {
        CountLeadingOnesCorrect(testCases[i]);
        var result := ComputeResult(testCases[i]);
        ComputeResultCorrect(testCases[i]);
        results := results + [result];
        i := i + 1;
    }
}
// </vc-code>

