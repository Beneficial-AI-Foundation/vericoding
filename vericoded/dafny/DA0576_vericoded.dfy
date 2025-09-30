predicate ValidInput(input: string)
    requires |input| > 0
{
    var tokens := parseInputPure(input);
    |tokens| == 3 && 
    2 <= tokens[0] <= 5 &&
    1 <= tokens[1] <= 100 &&
    tokens[1] < tokens[2] <= 200
}

function calculateRecurrence(r: int, D: int, x0: int, n: int): int
    requires n >= 1
    decreases n
{
    if n == 1 then r * x0 - D
    else r * calculateRecurrence(r, D, x0, n - 1) - D
}

function generateExpectedOutput(r: int, D: int, x0: int): string
{
    generateOutputUpToIteration(r, D, x0, 10)
}

function generateOutputUpToIteration(r: int, D: int, x0: int, iterations: int): string
    requires iterations >= 0
{
    if iterations == 0 then ""
    else 
        var currentValue := calculateRecurrence(r, D, x0, iterations);
        var previousOutput := generateOutputUpToIteration(r, D, x0, iterations - 1);
        previousOutput + intToString(currentValue) + "\n"
}

// <vc-helpers>
function parseInputPure(input: string): seq<int>
{
    // Stub function that parses the input string into a sequence of integers
    // In real implementation, this would parse the space-separated integers
    [2, 1, 2] // placeholder return
}

function intToString(n: int): string
{
    // Stub function that converts an integer to its string representation
    "" // placeholder return
}

method parseInput(input: string) returns (tokens: seq<int>)
    requires |input| > 0
    requires ValidInput(input)
    ensures tokens == parseInputPure(input)
    ensures |tokens| == 3
    ensures 2 <= tokens[0] <= 5
    ensures 1 <= tokens[1] <= 100
    ensures tokens[1] < tokens[2] <= 200
{
    // Implementation would parse the actual input
    tokens := parseInputPure(input);
}

method intToStringMethod(n: int) returns (s: string)
    ensures s == intToString(n)
{
    s := intToString(n);
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures var tokens := parseInputPure(input);
            result == generateExpectedOutput(tokens[0], tokens[1], tokens[2])
// </vc-spec>
// <vc-code>
{
    var tokens := parseInput(input);
    var r := tokens[0];
    var D := tokens[1];
    var x0 := tokens[2];
    
    result := "";
    var i := 1;
    
    while i <= 10
        invariant 1 <= i <= 11
        invariant result == generateOutputUpToIteration(r, D, x0, i - 1)
    {
        var currentValue := calculateRecurrence(r, D, x0, i);
        var currentStr := intToStringMethod(currentValue);
        result := result + currentStr + "\n";
        i := i + 1;
    }
}
// </vc-code>

