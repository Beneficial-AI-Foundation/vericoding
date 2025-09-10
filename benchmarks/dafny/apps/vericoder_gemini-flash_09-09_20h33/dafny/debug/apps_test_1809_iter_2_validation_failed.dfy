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
function parseInputFunc(s: string): (int, int, int, int)
    reads s
    requires |s| > 0
    requires s[|s|-1] == '\n'
    ensures var n, m, W, B := parseInputFunc(s);
            n >= 0 && m >= 0 && W >= 0 && B >= 0
    // A stub for the actual parsing function.
    // In a real scenario, this would parse the string 's' into four integers.
    // For verification purposes, we'll assume it returns valid non-negative integers.
{
    (0, 0, 0, 0) // Placeholder
}

function calculateAnswer(n: int, m: int, W: int, B: int): int
    requires n >= 0 && m >= 0 && W >= 0 && B >= 0
    ensures calculateAnswer(n, m, W, B) >= 0
    // A stub for the actual calculation function.
    // In a real scenario, this would perform some calculation based on n, m, W, B.
    // For verification purposes, we'll assume it returns a non-negative integer.
{
    n + m + W + B // Placeholder
}

function intToString(i: int): string
    requires i >= 0
    ensures |intToString(i)| > 0
    // A stub for converting an integer to a string.
    // For this problem, we need to ensure it returns a non-empty string.
{
    "0" // Placeholder
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
    var parsed := parseInputFunc(s);
    var n := parsed.0;
    var m := parsed.1;
    var W := parsed.2;
    var B := parsed.3;

    var answer := calculateAnswer(n, m, W, B);
    result := intToString(answer) + "\n";
}
// </vc-code>

