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
function parseInputPure(input: string): seq<int>
    requires |input| > 0
{
    var parts := splitString(input, ' ');
    if |parts| >= 3 then
        [stringToInt(parts[0]), stringToInt(parts[1]), stringToInt(parts[2])]
    else
        [0, 0, 0]
}

function splitString(s: string, delimiter: char): seq<string>
{
    if |s| == 0 then []
    else
        var delimiterIndex := findDelimiter(s, delimiter, 0);
        if delimiterIndex == -1 then [s]
        else if delimiterIndex >= 0 && delimiterIndex < |s| then
            var firstPart := s[0..delimiterIndex];
            var remaining := s[delimiterIndex + 1..];
            [firstPart] + splitString(remaining, delimiter)
        else [s]
}

function findDelimiter(s: string, delimiter: char, start: int): int
    requires 0 <= start <= |s|
    decreases |s| - start
{
    if start >= |s| then -1
    else if s[start] == delimiter then start
    else findDelimiter(s, delimiter, start + 1)
}

function stringToInt(s: string): int
{
    if |s| == 0 then 0
    else if |s| == 1 then charToDigit(s[0])
    else if |s| == 2 then charToDigit(s[0]) * 10 + charToDigit(s[1])
    else if |s| == 3 then charToDigit(s[0]) * 100 + charToDigit(s[1]) * 10 + charToDigit(s[2])
    else 0
}

function charToDigit(c: char): int
{
    if c == '0' then 0
    else if c == '1' then 1
    else if c == '2' then 2
    else if c == '3' then 3
    else if c == '4' then 4
    else if c == '5' then 5
    else if c == '6' then 6
    else if c == '7' then 7
    else if c == '8' then 8
    else if c == '9' then 9
    else 0
}

function intToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + intToStringHelper(-n)
    else intToStringHelper(n)
}

function intToStringHelper(n: int): string
    requires n >= 0
{
    if n == 0 then ""
    else if n < 10 then [digitToChar(n)]
    else intToStringHelper(n / 10) + [digitToChar(n % 10)]
}

function digitToChar(d: int): char
    requires 0 <= d <= 9
{
    if d == 0 then '0'
    else if d == 1 then '1'
    else if d == 2 then '2'
    else if d == 3 then '3'
    else if d == 4 then '4'
    else if d == 5 then '5'
    else if d == 6 then '6'
    else if d == 7 then '7'
    else if d == 8 then '8'
    else '9'
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
    result := generateExpectedOutput(r, D, x0);
}
// </vc-code>

