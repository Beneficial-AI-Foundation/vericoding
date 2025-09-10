predicate ValidInput(dateStr: string) 
{
    |dateStr| == 10 && dateStr[0..4] == "2017"
}

predicate ValidOutput(input: string, output: string)
    requires |input| >= 4
{
    output == "2018" + input[4..] &&
    |output| == 10 &&
    output[0..4] == "2018" &&
    output[4..] == input[4..]
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(dateStr: string) returns (result: string)
    requires ValidInput(dateStr)
    ensures ValidOutput(dateStr, result)
// </vc-spec>
// <vc-code>
{
    result := "2018" + dateStr[4..];
}
// </vc-code>

