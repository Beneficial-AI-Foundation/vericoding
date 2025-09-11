// <vc-preamble>
predicate ValidInput(input: string)
{
    (|input| == 3 && input[1] == ' ') || 
    (|input| == 4 && input[1] == ' ' && input[3] == '\n')
}

predicate ValidHexDigit(c: char)
{
    c in {'A', 'B', 'C', 'D', 'E', 'F'}
}

predicate ValidInputFormat(input: string)
{
    |input| >= 3 &&
    ValidInput(input) &&
    ValidHexDigit(input[0]) &&
    ValidHexDigit(input[2])
}

predicate CorrectComparison(x: char, y: char, result: string)
{
    result in {"<\n", ">\n", "=\n"} &&
    ((x as int < y as int) <==> (result == "<\n")) &&
    ((x as int > y as int) <==> (result == ">\n")) &&
    ((x as int == y as int) <==> (result == "=\n"))
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInputFormat(stdin_input)
    ensures CorrectComparison(stdin_input[0], stdin_input[2], result)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
