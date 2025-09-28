// <vc-preamble>
predicate ValidInput(input: string)
{
    |input| >= 3 &&
    forall i :: 0 <= i < 3 ==> (input[i] == '1' || input[i] == '9')
}

function SwapDigit(c: char): char
    requires c == '1' || c == '9'
{
    if c == '1' then '9' else '1'
}

function TransformString(s: string): string
    requires |s| >= 3
    requires forall i :: 0 <= i < 3 ==> (s[i] == '1' || s[i] == '9')
{
    [SwapDigit(s[0]), SwapDigit(s[1]), SwapDigit(s[2])]
}

predicate ValidOutput(input: string, result: string)
    requires ValidInput(input)
{
    |result| == 4 &&
    result[3] == '\n' &&
    forall i :: 0 <= i < 3 ==> 
        (input[i] == '1' ==> result[i] == '9') && 
        (input[i] == '9' ==> result[i] == '1')
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Removed the helper function as it was not used and was a duplicate of an existing function. */
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(input, result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Converted the characters to strings before concatenating to resolve type mismatch. */
{
  var transformedChars: string := TransformString(input);
  result := transformedChars[0..1] + transformedChars[1..2] + transformedChars[2..3] + "\n";
}
// </vc-code>
