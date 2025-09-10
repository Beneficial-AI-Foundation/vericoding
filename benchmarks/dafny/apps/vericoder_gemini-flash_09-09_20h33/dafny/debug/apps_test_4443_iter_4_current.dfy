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
function NextCharAsString(c: char): string
    requires 'a' <= c <= 'y'
    ensures |NextCharAsString(c)| == 1
    ensures 'b' <= NextChar(c) <= 'z'
    ensures NextCharAsString(c)[0] == NextChar(c)
{
    var nextC := NextChar(c);
    if ('a' <= nextC <= 'z') then
        [nextC] // Convert char to single-character string
    else
        // This case should not be reachable given the `ensures` clause and `NextChar` definition.
        // However, Dafny requires all possible execution paths to return a value.
        // A more robust solution might involve `assert false;` if this were truly unreachable.
        // For now, returning a single character string to satisfy type constraints.
        ['?'] // Convert char to single-character string
    
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires ValidInput(input)
    ensures ValidOutput(input, output)
// </vc-spec>
// <vc-code>
{
    var nextChar_val := NextChar(input[0]);
    var nextCharStr_val := NextCharAsString(input[0]); // Use the helper function directly
    output := nextCharStr_val + ['\n']; // Concatenate string with single-character string
}
// </vc-code>

