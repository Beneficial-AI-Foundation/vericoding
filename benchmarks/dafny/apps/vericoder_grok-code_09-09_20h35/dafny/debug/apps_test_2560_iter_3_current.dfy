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
    if start >= |input| then []
    else
        var index := findIndex(input, start, '\n');
        if index >= |input| then
            [input[start..|input|]]
        else
            [input[start..index]] + SplitLinesAux(input, index+1)
}

function SplitSpaces(input: string): seq<string>
{
    SplitSpacesAux(input, 0)
}

function SplitSpacesAux(input: string, start: int): seq<string>
    requires 0 <= start <= |input|
    decreases |input| - start
{
    if start >= |input| then []
    else
        var index := findIndex(input, start, ' ');
        if index >= |input| then
            var part := input[start..|input|];
            if part != "" then [part] else []
        else
            var part := input[start..index];
            if part != "" then [part] + SplitSpacesAux(input, index+1)
            else SplitSpacesAux(input, index+1)
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
    assert str_t != "" && forall i :: 0 <= i < |str_t| ==> '0' <= str_t[i] <= '9' && !( |str_t|>1 && str_t[0] == '0' );
    var t := ParseInt(str_t);
    assert t < |lines| && 0 <= t;
    var i := 1;
    var result := "";
    while i <= t
        invariant 1 <= i <= t+1
        invariant |result| >= 0
        invariant forall j :: 0 <= j < |result| ==> result[j] in "Yes\nNo\n "
    {
        assert i < |lines|;
        var line := lines[i];
        var parts := SplitSpaces(line);
        assert |parts| >= 3;
        var str_n := parts[0];
        var str_l := parts[1];
        var str_r := parts[2];
        assert str_n != "" && forall i :: 0 <= i < |str_n| ==> '0' <= str_n[i] <= '9' && !( |str_n|>1 && str_n[0] == '0' );
        assert str_l != "" && forall i :: 0 <= i < |str_l| ==> '0' <= str_l[i] <= '9' && !( |str_l|>1 && str_l[0] == '0' );
        assert str_r != "" && forall i :: 0 <= i < |str_r| ==> '0' <= str_r[i] <= '9' && !( |str_r|>1 && str_r[0] == '0' );
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

