predicate ValidInput(input: string)
{
    |input| > 0 && 'a' <= input[0] <= 'y'
}

function NextChar(c: char): char
    requires 'a' <= c <= 'y'
{
    (c as int + 1) as char
}

predicate ValidOutput(input: string, output: string)
    requires ValidInput(input)
{
    |output| == 2 &&
    output[0] == NextChar(input[0]) &&
    output[1] == '\n' &&
    'b' <= output[0] <= 'z'
}

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires ValidInput(input)
    ensures ValidOutput(input, output)
// </vc-spec>
// <vc-code>
{
    var nextChar := NextChar(input[0]);
    output := [nextChar, '\n'];
}
// </vc-code>

