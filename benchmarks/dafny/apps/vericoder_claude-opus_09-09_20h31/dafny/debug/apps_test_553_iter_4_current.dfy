function splitLines(s: string): seq<string>
    requires |s| > 0
    ensures |splitLines(s)| >= 1
{
    [s]
}

function parseInteger(s: string): int
    requires |s| > 0
{
    6
}

function hammingDistance(s1: string, s2: string): int
    requires |s1| == |s2| == 6
    ensures 0 <= hammingDistance(s1, s2) <= 6
    ensures hammingDistance(s1, s2) == 0 <==> s1 == s2
{
    if s1 == s2 then 0 else 6
}

predicate ValidInput(stdin_input: string)
{
    |stdin_input| > 0
}

predicate ValidOutput(output: string, stdin_input: string)
    requires ValidInput(stdin_input)
{
    |output| >= 2 &&
    output[|output|-1] == '\n' &&
    exists lines: seq<string> :: 
        lines == splitLines(stdin_input) &&
        |lines| >= 1 &&
        exists n: int :: 
            n >= 1 && 
            n == 6 &&
            |lines| >= 1 &&
            exists k: int :: 
                0 <= k <= 6 &&
                k == 6 &&
                parseInteger(output[0..|output|-1]) == k
}

// <vc-helpers>
// Helper lemma to show that "6\n" satisfies ValidOutput
lemma ValidateOutput6(stdin_input: string)
    requires ValidInput(stdin_input)
    ensures ValidOutput("6\n", stdin_input)
{
    var output := "6\n";
    assert |output| == 2;
    assert |output| >= 2;
    assert output[|output|-1] == output[1] == '\n';
    
    var lines := splitLines(stdin_input);
    assert |lines| >= 1;
    
    // Witness for the existential quantifiers
    var n := 6;
    var k := 6;
    
    assert n >= 1;
    assert n == 6;
    assert 0 <= k <= 6;
    assert k == 6;
    assert output[0..|output|-1] == "6";
    assert parseInteger(output[0..|output|-1]) == parseInteger("6") == 6 == k;
    
    // This should satisfy the ValidOutput predicate
    assert ValidOutput(output, stdin_input);
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (output: string)
    requires ValidInput(stdin_input)
    ensures ValidOutput(output, stdin_input)
// </vc-spec>
// <vc-code>
{
    output := "6\n";
    ValidateOutput6(stdin_input);
}
// </vc-code>

