predicate ValidInput(test_cases: seq<(int, int)>)
{
    forall i :: 0 <= i < |test_cases| ==> 
        test_cases[i].0 > 0 && test_cases[i].1 > 0
}

function MinMovesToDivisible(a: int, b: int): int
    requires a > 0 && b > 0
{
    (b - a % b) % b
}

predicate ValidOutput(test_cases: seq<(int, int)>, results: seq<int>)
    requires ValidInput(test_cases)
{
    |results| == |test_cases| &&
    forall i :: 0 <= i < |results| ==> 
        results[i] == MinMovesToDivisible(test_cases[i].0, test_cases[i].1) &&
        results[i] >= 0
}

// <vc-helpers>
lemma ModLemma(a: int, b: int)
    requires a > 0 && b > 0
    ensures (b - a % b) % b == (if a % b == 0 then 0 else b - a % b)
{
}

lemma NonNegativeMinMoves(a: int, b: int)
    requires a > 0 && b > 0
    ensures MinMovesToDivisible(a, b) >= 0
{
    ModLemma(a, b);
}
// </vc-helpers>

// <vc-spec>
method solve(test_cases: seq<(int, int)>) returns (results: seq<int>)
    requires ValidInput(test_cases)
    ensures ValidOutput(test_cases, results)
// </vc-spec>
// <vc-code>
{
    results := [];
    var i := 0;
    while i < |test_cases|
        invariant i >= 0
        invariant |results| == i
        invariant ValidOutput(test_cases[0..i], results)
    {
        var a := test_cases[i].0;
        var b := test_cases[i].1;
        
        // Calculate the value using the helper function
        var res := MinMovesToDivisible(a, b);
        NonNegativeMinMoves(a, b);  // Prove the result is non-negative
        
        results := results + [res];
        i := i + 1;
    }
}
// </vc-code>

