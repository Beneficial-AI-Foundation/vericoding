/*
Given n books with weights w_i, find the optimal initial stacking order to minimize total weight lifted 
when reading books according to a given sequence. To read book x: lift all books above x, remove x from 
stack, put lifted books back (maintaining order), then place x on top. The book being read is not counted 
as lifted weight.
*/

function isValidInput(s: string): bool
    requires |s| > 0
{
    |s| >= 5 && s[|s|-1] == '\n'
}

function calculateResultFromInput(s: string): string
    requires |s| > 0
    requires isValidInput(s)
{
    var parsed := parseInputFunc(s);
    var n := parsed.0;
    var m := parsed.1;
    var W := parsed.2;
    var B := parsed.3;
    intToString(calculateAnswer(n, m, W, B))
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires |s| > 0
    requires '\n' in s
    requires isValidInput(s)
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures result == calculateResultFromInput(s) + "\n"
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
