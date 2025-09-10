predicate ValidInputFormat(input: string)
{
    var lines := SplitLines(input);
    |lines| >= 2 && 
    var first_line := ParseIntegers(lines[0]);
    |first_line| == 2 &&
    var n := first_line[0];
    var m := first_line[1];
    n >= 1 && m >= 0 &&
    |ParseIntegers(lines[1])| == n &&
    IsValidPermutation(ParseIntegers(lines[1]), n) &&
    |lines| == 2 + m &&
    (forall i :: 2 <= i < |lines| ==> 
        var query := ParseIntegers(lines[i]);
        |query| == 3 &&
        var l := query[0];
        var r := query[1];
        var x := query[2];
        1 <= l <= x <= r <= n)
}

predicate IsValidPermutation(p: seq<int>, n: int)
{
    |p| == n && 
    (forall i :: 0 <= i < |p| ==> 1 <= p[i] <= n) &&
    (forall i, j :: 0 <= i < j < |p| ==> p[i] != p[j])
}

predicate ValidOutputFormat(output: string)
{
    var lines := SplitLines(output);
    forall line :: line in lines ==> line == "Yes" || line == "No"
}

predicate OutputMatchesQueries(input: string, output: string)
{
    var input_lines := SplitLines(input);
    var output_lines := SplitLines(output);
    if |input_lines| < 2 then false
    else
        var first_line := ParseIntegers(input_lines[0]);
        if |first_line| != 2 then false
        else
            var n := first_line[0];
            var m := first_line[1];
            |input_lines| == 2 + m &&
            |output_lines| == m &&
            var p := ParseIntegers(input_lines[1]);
            forall i :: 0 <= i < m ==> 
                var query := ParseIntegers(input_lines[2 + i]);
                var l := query[0];
                var r := query[1]; 
                var x := query[2];
                var px := p[x - 1];
                var cnt := l + CountSmallerInRange(p, l - 1, r - 1, px);
                output_lines[i] == (if cnt == x then "Yes" else "No")
}

function CountSmallerInRange(p: seq<int>, start: int, end: int, value: int): int
    decreases if start <= end then end - start + 1 else 0
{
    if start > end then 0
    else if start < 0 || start >= |p| then 0
    else (if p[start] < value then 1 else 0) + CountSmallerInRange(p, start + 1, end, value)
}

function ParseIntegers(line: string): seq<int>
{
    []
}

function SplitLines(s: string): seq<string>
{
    if |s| == 0 then []
    else
        var idx := FindNewline(s, 0);
        if idx == -1 then [s]
        else [s[0..idx]] + SplitLines(s[idx+1..])
}

function FindNewline(s: string, start: nat): int
    requires start <= |s|
    ensures FindNewline(s, start) == -1 || (start <= FindNewline(s, start) < |s|)
    decreases |s| - start
{
    if start >= |s| then -1
    else if s[start] == '\n' then start
    else FindNewline(s, start + 1)
}

// <vc-helpers>
lemma ValidOutputFormatHelper(lines: seq<string>)
    requires forall line :: line in lines ==> line == "Yes" || line == "No"
    ensures ValidOutputFormat(JoinLines(lines))
{
    assert SplitLines(JoinLines(lines)) == lines;
}

function JoinLines(lines: seq<string>): string
{
    if |lines| == 0 then ""
    else if |lines| == 1 then lines[0] + "\n"
    else lines[0] + "\n" + JoinLines(lines[1..])
}

lemma JoinSplitLinesIdentity(lines: seq<string>)
    requires forall line :: line in lines ==> '\n' !in line
    ensures SplitLines(JoinLines(lines)) == lines
{
    if |lines| == 0 {
        assert JoinLines(lines) == "";
        assert SplitLines("") == [];
    } else if |lines| == 1 {
        var joined := JoinLines(lines);
        assert joined == lines[0] + "\n";
        assert SplitLines(joined) == [lines[0]];
    } else {
        var rest := JoinLines(lines[1..]);
        JoinSplitLinesIdentity(lines[1..]);
        var joined := lines[0] + "\n" + rest;
        assert SplitLines(joined) == [lines[0]] + SplitLines(rest);
        assert SplitLines(rest) == lines[1..];
        assert SplitLines(joined) == [lines[0]] + lines[1..] == lines;
    }
}

lemma JoinLinesProperties(lines: seq<string>)
    requires |lines| > 0
    requires forall line :: line in lines ==> '\n' !in line
    ensures var result := JoinLines(lines); |result| > 0 && result[|result|-1] == '\n'
    ensures forall i :: 0 <= i < |JoinLines(lines)| ==> JoinLines(lines)[i] in "YesNo \n"
    requires forall line :: line in lines ==> line == "Yes" || line == "No"
{
    var result := JoinLines(lines);
    if |lines| == 1 {
        assert result == lines[0] + "\n";
        assert |result| > 0 && result[|result|-1] == '\n';
    } else {
        JoinLinesProperties(lines[1..]);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires '\n' in stdin_input
    requires ValidInputFormat(stdin_input)
    ensures |result| > 0
    ensures forall i :: 0 <= i < |result| ==> result[i] in "YesNo \n"
    ensures result != "" ==> result[|result|-1] == '\n'
    ensures ValidOutputFormat(result)
    ensures OutputMatchesQueries(stdin_input, result)
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(stdin_input);
    var first_line := ParseIntegers(lines[0]);
    var n := first_line[0];
    var m := first_line[1];
    var p := ParseIntegers(lines[1]);
    
    var results: seq<string> := [];
    var i := 0;
    
    while i < m
        invariant 0 <= i <= m
        invariant |results| == i
        invariant forall j :: 0 <= j < |results| ==> results[j] == "Yes" || results[j] == "No"
        invariant forall j :: 0 <= j < i ==> 
            var query := ParseIntegers(lines[2 + j]);
            var l := query[0];
            var r := query[1]; 
            var x := query[2];
            var px := p[x - 1];
            var cnt := l + CountSmallerInRange(p, l - 1, r - 1, px);
            results[j] == (if cnt == x then "Yes" else "No")
    {
        var query := ParseIntegers(lines[2 + i]);
        var l := query[0];
        var r := query[1];
        var x := query[2];
        var px := p[x - 1];
        var cnt := l + CountSmallerInRange(p, l - 1, r - 1, px);
        
        if cnt == x {
            results := results + ["Yes"];
        } else {
            results := results + ["No"];
        }
        i := i + 1;
    }
    
    assert |results| == m;
    assert forall j :: 0 <= j < |results| ==> results[j] == "Yes" || results[j] == "No";
    
    JoinLinesProperties(results);
    ValidOutputFormatHelper(results);
    JoinSplitLinesIdentity(results);
    
    result := JoinLines(results);
}
// </vc-code>

