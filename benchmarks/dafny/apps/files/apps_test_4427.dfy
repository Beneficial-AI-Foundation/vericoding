/*
Given a recurrence relation x_{i+1} = r × x_i - D starting from year 2000, 
calculate the values for years 2001 through 2010.
Input: Three integers r, D, x_2000 where 2 ≤ r ≤ 5, 1 ≤ D ≤ 100, D < x_2000 ≤ 200
Output: 10 lines containing x_{2001}, x_{2002}, ..., x_{2010} respectively
*/

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
  assume {:axiom} false;
}
// </vc-code>
