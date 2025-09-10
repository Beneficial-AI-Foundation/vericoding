predicate ValidInput(trainFare: int, busFare: int)
{
    1 <= trainFare <= 100 && 1 <= busFare <= 100 && busFare % 2 == 0
}

function TotalCost(trainFare: int, busFare: int): int
    requires ValidInput(trainFare, busFare)
{
    trainFare + busFare / 2
}

// <vc-helpers>
function replace(s: string, oldChar: char, newChar: char): string
{
    if |s| == 0 then ""
    else if s[0] == oldChar then [newChar] + replace(s[1..], oldChar, newChar)
    else [s[0]] + replace(s[1..], oldChar, newChar)
}

function removeNewlines(s: string): string
{
    if |s| == 0 then ""
    else if s[0] == '\n' then removeNewlines(s[1..])
    else [s[0]] + removeNewlines(s[1..])
}

function split(s: string, delimiter: char): seq<string>
    ensures |split(s, delimiter)| >= 1
{
    splitHelper(s, delimiter, 0, [])
}

function splitHelper(s: string, delimiter: char, start: int, acc: seq<string>): seq<string>
    requires 0 <= start <= |s|
    ensures |splitHelper(s, delimiter, start, acc)| >= |acc| + 1
    decreases |s| - start
{
    if start >= |s| then acc + [s[start..]]
    else if s[start] == delimiter then splitHelper(s, delimiter, start + 1, acc + [s[start..start]])
    else splitHelperNonDelim(s, delimiter, start, start + 1, acc)
}

function splitHelperNonDelim(s: string, delimiter: char, start: int, i: int, acc: seq<string>): seq<string>
    requires 0 <= start <= i <= |s|
    ensures |splitHelperNonDelim(s, delimiter, start, i, acc)| >= |acc| + 1
    decreases |s| - i
{
    if i >= |s| then acc + [s[start..i]]
    else if s[i] == delimiter then splitHelper(s, delimiter, i + 1, acc + [s[start..i]])
    else splitHelperNonDelim(s, delimiter, start, i + 1, acc)
}

predicate isValidInteger(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function stringToInt(s: string): int
    requires isValidInteger(s)
{
    stringToIntHelper(s, 0)
}

function stringToIntHelper(s: string, acc: int): int
    requires isValidInteger(s)
    decreases |s|
{
    if |s| == 0 then acc
    else stringToIntHelper(s[1..], acc * 10 + (s[0] - '0') as int)
}

function intToString(n: int): string
    requires n >= 0
{
    if n == 0 then "0"
    else if n < 10 then [(n as char + '0')]
    else intToString(n / 10) + [(n % 10) as char + '0']
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires exists i :: 0 <= i < |input| && input[i] == ' '
    requires var parts := split(replace(input, "\n", ""), ' '); 
             |parts| >= 2 && 
             isValidInteger(parts[0]) && 
             isValidInteger(parts[1])
    requires var parts := split(replace(input, "\n", ""), ' ');
             var trainFare := stringToInt(parts[0]);
             var busFare := stringToInt(parts[1]);
             ValidInput(trainFare, busFare)
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures var parts := split(replace(input, "\n", ""), ' ');
            var trainFare := stringToInt(parts[0]);
            var busFare := stringToInt(parts[1]);
            result == intToString(TotalCost(trainFare, busFare)) + "\n"
// </vc-spec>
// <vc-code>
{
    var cleanInput := removeNewlines(input);
    var parts := split(cleanInput, ' ');
    var trainFare := stringToInt(parts[0]);
    var busFare := stringToInt(parts[1]);
    var totalCost := TotalCost(trainFare, busFare);
    result := intToString(totalCost) + "\n";
}
// </vc-code>

