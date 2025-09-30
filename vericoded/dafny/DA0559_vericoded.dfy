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
function replace(s: seq<char>, oldSeq: seq<char>, newSeq: seq<char>): seq<char>
    decreases |s|
{
    if |oldSeq| == 0 then s
    else if |s| < |oldSeq| then s
    else if s[..|oldSeq|] == oldSeq then newSeq + replace(s[|oldSeq|..], oldSeq, newSeq)
    else [s[0]] + replace(s[1..], oldSeq, newSeq)
}

function indexOf(s: seq<char>, c: char): int
    requires exists i :: 0 <= i < |s| && s[i] == c
    ensures 0 <= indexOf(s, c) < |s| && s[indexOf(s, c)] == c
    decreases |s|
{
    if s[0] == c then 0 else 1 + indexOf(s[1..], c)
}

function split(s: seq<char>, c: char): seq<seq<char>>
    decreases |s|
{
    if exists i :: 0 <= i < |s| && s[i] == c then
        var idx := indexOf(s, c);
        var left := s[..idx];
        var right := s[idx + 1..];
        [left] + split(right, c)
    else
        [s]
}

function digitToChar(n: int): char
    requires 0 <= n <= 9
{
    ((n + ('0' as int)) as char)
}

function intToString(n: int): seq<char>
    requires n >= 0
    decreases n
{
    if n < 10 then [digitToChar(n)]
    else intToString(n / 10) + [digitToChar(n % 10)]
}

function stringToInt(s: seq<char>): int
    requires |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    decreases |s|
{
    if |s| == 1 then (s[0] as int) - ('0' as int)
    else 10 * stringToInt(s[..|s|-1]) + ((s[|s|-1] as int) - ('0' as int))
}

predicate isValidInteger(s: seq<char>) {
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
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
    var cleaned := replace(input, "\n", []);
    var parts := split(cleaned, ' ');
    var trainFare := stringToInt(parts[0]);
    var busFare := stringToInt(parts[1]);
    var total := TotalCost(trainFare, busFare);
    result := intToString(total) + "\n";
}
// </vc-code>

