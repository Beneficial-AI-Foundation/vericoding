Calculate the total cost to travel from Station A to Station C using a special discount ticket.
Given train fare X yen (A to B) and bus fare Y yen (B to C), if you take the train first then the bus,
the bus fare becomes half price. Find the total cost A to C.

predicate ValidInput(trainFare: int, busFare: int)
{
    1 <= trainFare <= 100 && 1 <= busFare <= 100 && busFare % 2 == 0
}

function TotalCost(trainFare: int, busFare: int): int
    requires ValidInput(trainFare, busFare)
{
    trainFare + busFare / 2
}

function isValidInteger(s: string): bool
{
    |s| > 0 && (s[0] != '-' || |s| > 1) && 
    forall i :: 0 <= i < |s| ==> (i == 0 && s[i] == '-') || ('0' <= s[i] <= '9')
}

function replace(s: string, target: string, replacement: string): string
    requires |target| > 0
    decreases |s|
{
    if |s| < |target| then s
    else if s[..|target|] == target then replacement + replace(s[|target|..], target, replacement)
    else s[..1] + replace(s[1..], target, replacement)
}

function intToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + intToStringHelper(-n)
    else intToStringHelper(n)
}

function intToStringHelper(n: int): string
    requires n > 0
{
    if n < 10 then [('0' as int + n) as char]
    else intToStringHelper(n / 10) + [('0' as int + n % 10) as char]
}

function split(s: string, delimiter: char): seq<string>
{
    if |s| == 0 then
        [""]
    else if s[0] == delimiter then
        [""] + split(s[1..], delimiter)
    else
        var rest := split(s[1..], delimiter);
        if |rest| == 0 then [s] else [s[0..1] + rest[0]] + rest[1..]
}

function stringToInt(s: string): int
{
    if |s| == 0 then 0
    else if s[0] == '-' then -stringToIntHelper(s[1..])
    else stringToIntHelper(s)
}

function stringToIntHelper(s: string): int
{
    if |s| == 0 then 0
    else if |s| == 1 then charToInt(s[0])
    else stringToIntHelper(s[..|s|-1]) * 10 + charToInt(s[|s|-1])
}

function charToInt(c: char): int
{
    c as int - '0' as int
}

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
{
    var cleanInput := replace(input, "\n", "");
    var parts := split(cleanInput, ' ');

    var trainFare := stringToInt(parts[0]);
    var busFare := stringToInt(parts[1]);

    var totalCost := TotalCost(trainFare, busFare);
    result := intToString(totalCost) + "\n";
}
