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
    reads input
    ensures var tokens := parseInputPure(input);
            (|tokens| == 3 &&
            int.Parse(input.Split(' ')[0]) == tokens[0] &&
            int.Parse(input.Split(' ')[1]) == tokens[1] &&
            int.Parse(input.Split(' ')[2]) == tokens[2]) ||
            (|tokens| != 3 && tokens == [])
{
    var parts := input.Split(' ');
    if |parts| != 3 then []
    else
        var r := int.Parse(parts[0]);
        var D := int.Parse(parts[1]);
        var x0 := int.Parse(parts[2]);
        [r, D, x0]
}

function intToString(i: int): string
  ensures forall x: int :: x == i ==> var s := intToString(x); int.Parse(s) == x
{
  i as string
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
    var tokens := parseInputPure(input);
    var r := tokens[0];
    var D := tokens[1];
    var x0 := tokens[2];
    result := generateExpectedOutput(r, D, x0);
}
// </vc-code>

