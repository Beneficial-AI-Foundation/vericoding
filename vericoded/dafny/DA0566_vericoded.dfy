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
lemma MinMovesProperties(a: int, b: int)
    requires a > 0 && b > 0
    ensures MinMovesToDivisible(a, b) >= 0
    ensures MinMovesToDivisible(a, b) < b
{
    var remainder := a % b;
    assert 0 <= remainder < b;
    var moves := (b - remainder) % b;
    if remainder == 0 {
        assert moves == b % b == 0;
    } else {
        assert 0 < remainder < b;
        assert 0 < b - remainder < b;
        assert moves == b - remainder;
    }
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
        invariant 0 <= i <= |test_cases|
        invariant |results| == i
        invariant forall j :: 0 <= j < i ==> 
            results[j] == MinMovesToDivisible(test_cases[j].0, test_cases[j].1)
        invariant forall j :: 0 <= j < i ==> results[j] >= 0
    {
        var a := test_cases[i].0;
        var b := test_cases[i].1;
        var moves := (b - a % b) % b;
        
        assert moves == MinMovesToDivisible(a, b);
        MinMovesProperties(a, b);
        
        results := results + [moves];
        i := i + 1;
    }
}
// </vc-code>

