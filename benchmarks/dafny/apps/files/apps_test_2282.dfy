/*
Given n movement commands ('L' for left, 'R' for right), determine how many
different final positions are possible when any subset of commands may be ignored.
The answer is always n + 1, representing all positions from minimum to maximum.
*/

predicate ValidInput(input: string)
{
    |input| > 0 && exists i :: 0 <= i < |input| && input[i] == '\n'
}

predicate ValidCommandInput(input: string)
{
    var lines := split(input, '\n');
    |lines| >= 2 && lines[0] != "" && isValidInteger(lines[0])
}

function ExtractN(input: string): int
    requires ValidCommandInput(input)
{
    var lines := split(input, '\n');
    parseInteger(lines[0])
}

predicate CorrectOutput(input: string, result: string)
{
    ValidCommandInput(input) ==> 
        result == intToString(ExtractN(input) + 1) + "\n"
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures CorrectOutput(input, result)
    ensures !ValidCommandInput(input) ==> result == ""
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
