// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Removed comment placeholders */

// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures result == ExpectedOutput(input)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed compilation error by adding braces in if statement */
{
  var s := NormalizeInput(input);
  if s == "ABC" {
    result := "ARC\n";
  } else {
    result := "ABC\n";
  }
}
// </vc-code>
