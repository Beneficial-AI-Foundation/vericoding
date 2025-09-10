predicate ValidInput(input: string)
    requires |input| > 0
{
    var tokens := parseInputPure(input);
    |tokens| == 3 && 
    2 <= tokens[0] <= 5 &&
    1 <= tokens[1] <= 100 &&
    tokens[1] < tokens[2] <= 200
}

function calculateRecurrence(r: int, D: int, x0: int, n: int): int
    requires n >= 1
    decreases n
{
    if n == 1 then r * x0 - D
    else r * calculateRecurrence(r, D, x0, n - 1) - D
}

function generateExpectedOutput(r: int, D: int, x0: int): string
{
    generateOutputUpToIteration(r, D, x0, 10)
}

function generateOutputUpToIteration(r: int, D: int, x0: int, iterations: int): string
    requires iterations >= 0
{
    if iterations == 0 then ""
    else 
        var currentValue := calculateRecurrence(r, D, x0, iterations);
        var previousOutput := generateOutputUpToIteration(r, D, x0, iterations - 1);
        previousOutput + intToString(currentValue) + "\n"
}

// <vc-helpers>
lemma calculateRecurrenceClosedForm(r: int, D: int, x0: int, n: int) returns (result: int)
    requires n >= 1
    ensures result == calculateRecurrence(r, D, x0, n)
    decreases n
{
    if n == 1 {
        result := r * x0 - D;
    } else {
        var prev := calculateRecurrenceClosedForm(r, D, x0, n - 1);
        result := r * prev - D;
    }
}

function intToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + intToString(-n)
    else if n < 10 then [digitToChar(n)]
    else intToString(n / 10) + [digitToChar(n % 10)]
}

function digitToChar(d: int): char
    requires 0 <= d < 10
{
    ['0','1','2','3','4','5','6','7','8','9'][d]
}

function parseInputPure(input: string): seq<int>
    ensures |result| == 3
{
    var parts := split(input, ' ');
    assert |parts| == 3;
    [stringToInt(parts[0]), stringToInt(parts[1]), stringToInt(parts[2])]
}

function stringToInt(s: string): int
    requires |s| > 0
{
    if |s| == 1 then charToDigit(s[0])
    else 10 * stringToInt(s[..|s|-1]) + charToDigit(s[|s|-1])
}

function charToDigit(c: char): int
    requires '0' <= c <= '9'
{
    c as int - '0' as int
}

function split(s: string, sep: char): seq<string>
    decreases |s|
{
    if |s| == 0 then []
    else
        var idx := findFirst(s, sep);
        if idx == -1 then [s]
        else [s[..idx]] + split(s[idx+1..], sep)
}

function findFirst(s: string, c: char): int
    ensures res == -1 || 0 <= res < |s|
{
    if |s| == 0 then -1
    else if s[0] == c then 0
    else
        var rest := findFirst(s[1..], c);
        if rest == -1 then -1 else rest + 1
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures var tokens := parseInputPure(input);
            result == generateExpectedOutput(tokens[0], tokens[1], tokens[2])
// </vc-spec>
// <vc-code>
{
    var tokens := parseInputPure(input);
    var r := tokens[0];
    var D := tokens[1];
    var x0 := tokens[2];
    
    var output := "";
    var x := x0;
    
    var i := 1;
    while i <= 10
        invariant 1 <= i <= 11
        invariant output == generateOutputUpToIteration(r, D, x0, i - 1)
        decreases 11 - i
    {
        x := r * x - D;
        output := output + intToString(x) + "\n";
        i := i + 1;
    }
    
    return output;
}
// </vc-code>

