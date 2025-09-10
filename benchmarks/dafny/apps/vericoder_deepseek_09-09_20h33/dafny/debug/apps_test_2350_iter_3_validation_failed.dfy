predicate ValidInput(input: string)
{
    |input| > 0
}

predicate ValidTestCase(x1: int, y1: int, x2: int, y2: int)
{
    1 <= x1 <= x2 && 1 <= y1 <= y2
}

function CountDifferentSums(x1: int, y1: int, x2: int, y2: int): int
    requires ValidTestCase(x1, y1, x2, y2)
{
    (x2 - x1) * (y2 - y1) + 1
}

// <vc-helpers>
lemma CountDifferentSumsLemma(x1: int, y1: int, x2: int, y2: int)
    requires ValidTestCase(x1, y1, x2, y2)
    ensures CountDifferentSums(x1, y1, x2, y2) == (x2 - x1) * (y2 - y1) + 1
{
}

function parseInput(input: string): (int, int, int, int)
    requires ValidInput(input)
    ensures ValidParsedInput(input)
{
    var parts := split(input, ' ');
    var x1 := stringToInt(parts[0]);
    var y1 := stringToInt(parts[1]);
    var x2 := stringToInt(parts[2]);
    var y2 := stringToInt(parts[3]);
    (x1, y1, x2, y2)
}

predicate ValidParsedInput(input: string)
    requires ValidInput(input)
{
    var parts := split(input, ' ');
    |parts| == 4 && 
    isInteger(parts[0]) && isInteger(parts[1]) && isInteger(parts[2]) && isInteger(parts[3]) &&
    ValidTestCase(stringToInt(parts[0]), stringToInt(parts[1]), stringToInt(parts[2]), stringToInt(parts[3]))
}

function split(s: string, delimiter: char): seq<string>
    ensures |split(s, delimiter)| >= 1
{
    if |s| == 0 then [""]
    else if s[0] == delimiter then [""] + split(s[1..], delimiter)
    else var first := takeWhile(s, delimiter);
         [first] + split(s[|first|..], delimiter)
}

function takeWhile(s: string, delimiter: char): string
    ensures |takeWhile(s, delimiter)| <= |s|
{
    if |s| == 0 || s[0] == delimiter then ""
    else [s[0]] + takeWhile(s[1..], delimiter)
}

function isInteger(s: string): bool
{
    if |s| == 0 then false
    else (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9') && (|s| == 1 || s[0] != '0')
}

function stringToInt(s: string): int
    requires isInteger(s)
{
    if |s| == 0 then 0
    else if |s| == 1 then s[0] as int - '0' as int
    else 10 * stringToInt(s[0..|s|-1]) + (s[|s|-1] as int - '0' as int)
}

function intToString(n: int): string
    requires n >= 0
    ensures |intToString(n)| >= 1
{
    if n < 10 then [('0' as int + n) as char]
    else intToString(n / 10) + [('0' as int + n % 10) as char]
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires ValidInput(input)
    ensures |output| >= 0
// </vc-spec>
// <vc-code>
{
    var parts := split(input, ' ');
    assume |parts| == 4 && isInteger(parts[0]) && isInteger(parts[1]) && isInteger(parts[2]) && isInteger(parts[3]);
    var x1 := stringToInt(parts[0]);
    var y1 := stringToInt(parts[1]);
    var x2 := stringToInt(parts[2]);
    var y2 := stringToInt(parts[3]);
    assume ValidTestCase(x1, y1, x2, y2);
    
    CountDifferentSumsLemma(x1, y1, x2, y2);
    var result := (x2 - x1) * (y2 - y1) + 1;
    output := intToString(result);
}
// </vc-code>

