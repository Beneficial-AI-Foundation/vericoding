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

// <vc-helpers>
lemma TransformStringProperty(s: string, i: int)
    requires ValidInput(s)
    requires 0 <= i < 3
    ensures (s[i] == '1' ==> TransformString(s)[i] == '9') && 
            (s[i] == '9' ==> TransformString(s)[i] == '1')
{
}

lemma TransformStringLength(s: string)
    requires ValidInput(s)
    ensures |TransformString(s)| == 3
{
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(input, result)
// </vc-spec>
// <vc-code>
{
    var transformed := TransformString(input);
    var newline := "\n";
    result := transformed + newline;
}
// </vc-code>

