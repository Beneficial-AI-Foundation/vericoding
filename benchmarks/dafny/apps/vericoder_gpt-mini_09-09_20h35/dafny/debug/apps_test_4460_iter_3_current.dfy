predicate validInput(s: string)
{
    |s| > 0 && (forall i :: 0 <= i < |s| ==> s[i] == ' ' || s[i] == '\n' || ('0' <= s[i] <= '9') || s[i] == '-')
}

predicate validNumber(s: string)
{
    |s| == 0 || (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9' || (i == 0 && s[i] == '-'))
}

function countZeros(numbers: seq<int>): int
{
    if |numbers| == 0 then 0
    else (if numbers[0] == 0 then 1 else 0) + countZeros(numbers[1..])
}

function findZeroIndex(numbers: seq<int>): int
    requires |numbers| > 0
    requires countZeros(numbers) == 1
{
    if numbers[0] == 0 then 0
    else if |numbers| > 1 then 1 + findZeroIndex(numbers[1..])
    else 0
}

function parseInts(s: string): seq<int>
    requires |s| > 0
    requires validInput(s)
{
    parseIntsHelper(s, 0, "", [])
}

function generateOutput(numbers: seq<int>): string
{
    generateOutputHelper(numbers, 0, "")
}

// <vc-helpers>
function charToDigit(c: char): int
    requires '0' <= c <= '9'
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
    else 9
}

function parseInt(s: string): int
    requires |s| > 0
    requires validNumber(s)
    decreases |s|
{
    if s[0] == '-' then -parseInt(s[1..])
    else if |s| == 1 then charToDigit(s[0])
    else parseInt(s[..|s|-1]) * 10 + charToDigit(s[|s|-1])
}

function parseIntsHelper(s: string, i: int, cur: string, acc: seq<int>): seq<int>
    requires 0 <= i <= |s|
    requires validInput(s)
    decreases |s| - i
{
    if i == |s| then
        if |cur| == 0 then acc else acc + [parseInt(cur)]
    else
        var c := s[i];
        if c == ' ' || c == '\n' then
            if |cur| == 0 then parseIntsHelper(s, i + 1, "", acc)
            else parseIntsHelper(s, i + 1, "", acc + [parseInt(cur)])
        else
            parseIntsHelper(s, i + 1, cur + s[i..i+1], acc)
}

function intToString(n: int): string
    decreases (if n < 0 then -n else n)
{
    if n == 0 then "0"
    else if n < 0 then "-" + intToString(-n)
    else if n < 10 then "0123456789"[n .. n + 1]
    else intToString(n / 10) + "0123456789"[n % 10 .. n % 10 + 1]
}

function generateOutputHelper(numbers: seq<int>, i: int, acc: string): string
{
    if countZeros(numbers) == 1 then intToString(findZeroIndex(numbers) + 1) else "0"
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires validInput(input)
    requires |input| > 0
    ensures var numbers := parseInts(input);
            result == generateOutput(numbers)
// </vc-spec>
// <vc-code>
{
  result := generateOutput(parseInts(input));
}
// </vc-code>

