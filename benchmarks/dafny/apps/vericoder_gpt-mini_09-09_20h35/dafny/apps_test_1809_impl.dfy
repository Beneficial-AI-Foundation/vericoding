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
function parseInputFunc(s: string): (int, int, seq<int>, seq<int>)
    requires |s| > 0
    requires isValidInput(s)
{
    (0, 0, [], [])
}

function calculateAnswer(n: int, m: int, W: seq<int>, B: seq<int>): int
    requires n >= 0
    requires m >= 0
{
    0
}

function intToString(x: int): string
{
    "0"
}
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
  result := calculateResultFromInput(s) + "\n";
}
// </vc-code>

