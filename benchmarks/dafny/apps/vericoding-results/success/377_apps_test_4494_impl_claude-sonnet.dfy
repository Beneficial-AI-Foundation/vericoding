predicate ValidInput(input: string)
{
    |input| > 0 && 
    (var s := if input[|input|-1] == '\n' then input[..|input|-1] else input;
     s == "ABC" || s == "ARC")
}

function NormalizeInput(input: string): string
    requires |input| > 0
{
    if input[|input|-1] == '\n' then input[..|input|-1] else input
}

function ExpectedOutput(input: string): string
    requires ValidInput(input)
{
    var s := NormalizeInput(input);
    if s == "ABC" then "ARC\n" else "ABC\n"
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures result == ExpectedOutput(input)
// </vc-spec>
// <vc-code>
{
    var s := NormalizeInput(input);
    if s == "ABC" {
        result := "ARC\n";
    } else {
        result := "ABC\n";
    }
}
// </vc-code>

