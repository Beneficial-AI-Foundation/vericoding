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
function findIndex(s: string, start: int, ch: char): int
    requires 0 <= start <= |s|
    decreases |s| - start
{
    if start == |s| then |s|
    else if s[start] == ch then start
    else findIndex(s, start+1, ch)
}

function SplitLines(input: string): seq<string>
{
    SplitLinesAux(input, 0)
}

function SplitLinesAux(input: string, start: int): seq<string>
    requires 0 <= start <= |input|
    decreases |input| - start
{
    if start == |input| then []
    else
        var index := findIndex(input, start, '\n');
        if index < |input| then [input[start..index]] + SplitLinesAux(input, index+1)
        else [input[start..]]
}

function SplitSpaces(input: string): seq<string>
{
    SplitSpacesAux(input, 0)
}

function SplitSpacesAux(input: string, start: int): seq<string>
    requires 0 <= start <= |input|
    decreases |input| - start
{
    if start == |input| then []
    else
        var index := findIndex(input, start, ' ');
        if index < |input| then
            var part := input[start..index];
            if part != "" then [part] + SplitSpacesAux(input, index+1)
            else SplitSpacesAux(input, index+1)
        else
            var part := input[start..];
            if part != "" then [part] else []
}

function ParseInt(s: string): int
    requires s != "" && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    requires !( |s|>1 && s[0] == '0' )
{
    ParseIntAux(s, 0)
}

function ParseIntAux(s: string, pos: int): int
    requires 0 <= pos <= |s|
    decreases |s| - pos
{
    if pos == |s| then 0
    else
        var digit := (s[pos] as int) - ('0' as int);
        ParseIntAux(s, pos+1) * 10 + digit
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
    var lines := SplitLines(input);
    var str_t := lines[0];
    var t := ParseInt(str_t);
    var i := 1;
    while i <= t
        invariant 1 <= i <= t+1
        invariant |result| >= 0
        invariant forall j :: 0 <= j < |result| ==> result[j] in "Yes\nNo\n "
    {
        var line := lines[i];
        var parts := SplitSpaces(line);
        var str_n := parts[0];
        var str_l := parts[1];
        var str_r := parts[2];
        var n := ParseInt(str_n);
        var l := ParseInt(str_l);
        var r := ParseInt(str_r);
        var can := CanMakeSum(n, l, r);
        var output := if can then "Yes\n" else "No\n";
        result := result + output;
        i := i+1;
    }
}
// </vc-code>

