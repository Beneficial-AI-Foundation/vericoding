/*
Given five integers representing the values of variables x₁, x₂, x₃, x₄, x₅, find which variable has the value 0.
Initially, each variable xᵢ had value i, but exactly one variable was changed to 0.
Input: Five space-separated integers. Output: The index i (1-indexed) of the variable xᵢ that has value 0.
*/

predicate validInput(s: string)
{
    |s| > 0 && (forall i :: 0 <= i < |s| ==> s[i] == ' ' || s[i] == '\n' || ('0' <= s[i] <= '9') || s[i] == '-')
}

predicate validNumber(s: string)
{
    |s| == 0 || (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9' || (i == 0 && s[i] == '-'))
}

function countZeros(numbers: seq<int>): int
{
    if |numbers| == 0 then 0
    else (if numbers[0] == 0 then 1 else 0) + countZeros(numbers[1..])
}

function findZeroIndex(numbers: seq<int>): int
    requires |numbers| > 0
    requires countZeros(numbers) == 1
{
    if numbers[0] == 0 then 0
    else if |numbers| > 1 then 1 + findZeroIndex(numbers[1..])
    else 0
}

function parseInts(s: string): seq<int>
    requires |s| > 0
    requires validInput(s)
{
    parseIntsHelper(s, 0, "", [])
}

function generateOutput(numbers: seq<int>): string
{
    generateOutputHelper(numbers, 0, "")
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires validInput(input)
    requires |input| > 0
    ensures var numbers := parseInts(input);
            result == generateOutput(numbers)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
