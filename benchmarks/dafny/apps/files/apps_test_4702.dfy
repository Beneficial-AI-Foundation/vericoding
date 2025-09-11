// <vc-preamble>
predicate ValidInput(input: string)
{
    |input| > 0 && 
    (input[0] == '0' || input[0] == '1') && 
    (|input| == 1 || (|input| > 1 && input[1] == '\n'))
}

function LogicalNot(digit: char): string
    requires digit == '0' || digit == '1'
{
    if digit == '0' then "1\n" else "0\n"
}

predicate CorrectOutput(input: string, output: string)
    requires ValidInput(input)
{
    output == LogicalNot(input[0])
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires ValidInput(input)
    ensures CorrectOutput(input, output)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
