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
    ensures CountLeadingOnes(piles) == 0 || (0 < CountLeadingOnes(piles) <= |piles| && piles[CountLeadingOnes(piles) - 1] == 1)
    ensures forall k :: 0 <= k < CountLeadingOnes(piles) ==> piles[k] == 1
{
    if |piles| == 0 {
    } else if piles[0] != 1 {
    } else {
        CountLeadingOnesCorrect(piles[1..]);
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
    for i := 0 to |testCases|
        invariant 0 <= i <= |testCases|
        invariant |results| == i
        invariant ValidResults(results)
        invariant forall j :: 0 <= j < i ==> CorrectGameResult(testCases[j], results[j])
    {
        var piles := testCases[i];
        var onesCount := 0;
        
        // Count the number of piles with value 1
        for k := 0 to |piles|
            invariant 0 <= k <= |piles|
            invariant onesCount == |set j | 0 <= j < k && piles[j] == 1|
        {
            if piles[k] == 1 {
                onesCount := onesCount + 1;
            }
        }
        
        assert onesCount == |set j | 0 <= j < |piles| && piles[j] == 1|;
        
        var allOnes := (onesCount == |piles|);
        var leadingOnes := CountLeadingOnes(piles);
        
        var result: string;
        if allOnes {
            if onesCount % 2 == 1 {
                result := "First";
            } else {
                result := "Second";
            }
        } else {
            if leadingOnes % 2 == 1 {
                result := "Second";
            } else {
                result := "First";
            }
        }
        
        assert CorrectGameResult(piles, result);
        results := results + [result];
    }
}
// </vc-code>

