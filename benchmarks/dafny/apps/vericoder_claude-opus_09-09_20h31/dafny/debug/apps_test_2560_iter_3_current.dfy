predicate ValidInput(input: string)
{
    |input| > 0
}

function CanMakeSum(n: int, l: int, r: int): bool
{
    l > 0 && l <= r && n > 0 && n % l <= (r - l) * (n / l)
}

predicate ValidOutput(result: string)
{
    |result| >= 0 && forall i :: 0 <= i < |result| ==> result[i] in "Yes\nNo\n "
}

predicate CorrectSolution(input: string, result: string)
{
    var lines := SplitLines(input);
    |lines| > 0 ==> 
    (var t := ParseInt(lines[0]);
     var outputLines := SplitLines(result);
     |outputLines| >= 1 && (|outputLines| == 1 ==> outputLines[0] == "") &&
     (|outputLines| > 1 ==> outputLines[|outputLines|-1] == "") &&
     forall i :: 1 <= i <= t && i < |lines| ==>
        (var parts := SplitSpaces(lines[i]);
         |parts| >= 3 ==>
         (var n := ParseInt(parts[0]);
          var l := ParseInt(parts[1]);
          var r := ParseInt(parts[2]);
          var expectedOutput := if CanMakeSum(n, l, r) then "Yes" else "No";
          i-1 < |outputLines| && outputLines[i-1] == expectedOutput)))
}

// <vc-helpers>
function SplitLines(s: string): seq<string>
{
    SplitBy(s, '\n')
}

function SplitSpaces(s: string): seq<string>
{
    SplitBy(s, ' ')
}

function SplitBy(s: string, delimiter: char): seq<string>
    decreases |s|
{
    if |s| == 0 then
        [""]
    else if s[|s|-1] == delimiter then
        SplitBy(s[..|s|-1], delimiter) + [""]
    else
        var parts := SplitBy(s[..|s|-1], delimiter);
        if |parts| == 0 then
            [s]
        else
            parts[..|parts|-1] + [parts[|parts|-1] + [s[|s|-1]]]
}

function ParseInt(s: string): int
{
    if |s| == 0 then
        0
    else if s[0] == '-' && |s| > 1 then
        var n := ParseNat(s[1..]);
        -(n as int)
    else
        ParseNat(s) as int
}

function ParseNat(s: string): nat
    decreases |s|
{
    if |s| == 0 then
        0
    else if '0' <= s[|s|-1] <= '9' then
        var digit := s[|s|-1] as int - '0' as int;
        ParseNat(s[..|s|-1]) * 10 + digit
    else
        0
}

method ParseIntMethod(s: string) returns (n: int)
    ensures n == ParseInt(s)
{
    n := ParseInt(s);
}

method SplitLinesMethod(s: string) returns (lines: seq<string>)
    ensures lines == SplitLines(s)
{
    lines := SplitLines(s);
}

method SplitSpacesMethod(s: string) returns (parts: seq<string>)
    ensures parts == SplitSpaces(s)
{
    parts := SplitSpaces(s);
}

lemma SplitLinesAppend(s: string, suffix: string)
    ensures SplitLines(s + suffix) == 
            if |suffix| == 0 then SplitLines(s)
            else if suffix == "\n" then SplitLines(s) + [""]
            else if |SplitLines(suffix)| > 0 then
                var sLines := SplitLines(s);
                var suffixLines := SplitLines(suffix);
                if |sLines| > 0 then
                    sLines[..|sLines|-1] + [sLines[|sLines|-1] + suffixLines[0]] + suffixLines[1..]
                else
                    suffixLines
            else SplitLines(s)
{
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(result)
    ensures CorrectSolution(input, result)
// </vc-spec>
// <vc-code>
{
    var lines := SplitLinesMethod(input);
    if |lines| == 0 {
        return "";
    }
    
    var t := ParseIntMethod(lines[0]);
    if t <= 0 {
        return "";
    }
    
    result := "";
    
    var i := 1;
    while i <= t && i < |lines|
        invariant 1 <= i <= t + 1
        invariant i <= |lines| || i == t + 1
        invariant ValidOutput(result)
        invariant var outputLines := SplitLines(result);
                  |outputLines| == i && 
                  (i == 1 ==> outputLines[0] == "") &&
                  (i > 1 ==> outputLines[i-1] == "") &&
                  forall j :: 1 <= j < i && j < |lines| ==>
                      (var parts := SplitSpaces(lines[j]);
                       |parts| >= 3 ==>
                       (var n := ParseInt(parts[0]);
                        var l := ParseInt(parts[1]);
                        var r := ParseInt(parts[2]);
                        var expectedOutput := if CanMakeSum(n, l, r) then "Yes" else "No";
                        j-1 < |outputLines| && outputLines[j-1] == expectedOutput))
    {
        var parts := SplitSpacesMethod(lines[i]);
        if |parts| >= 3 {
            var n := ParseIntMethod(parts[0]);
            var l := ParseIntMethod(parts[1]);
            var r := ParseIntMethod(parts[2]);
            
            var oldResult := result;
            var oldOutputLines := SplitLines(oldResult);
            
            if CanMakeSum(n, l, r) {
                result := result + "Yes\n";
            } else {
                result := result + "No\n";
            }
            
            SplitLinesAppend(oldResult, if CanMakeSum(n, l, r) then "Yes\n" else "No\n");
            assert SplitLines(result) == oldOutputLines + [if CanMakeSum(n, l, r) then "Yes" else ""] + [""];
        }
        i := i + 1;
    }
}
// </vc-code>

