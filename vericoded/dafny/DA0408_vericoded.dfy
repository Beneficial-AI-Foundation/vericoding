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
function IntToString(n: int): string
{
    if n == 0 then "0"
    else if n == 1 then "1"
    else if n == 2 then "2"
    else if n == 3 then "3"
    else if n == 4 then "4"
    else if n == 5 then "5"
    else if n == 6 then "6"
    else if n == 7 then "7"
    else if n == 8 then "8"
    else if n == 9 then "9"
    else "0" // fallback
}

lemma CountSmallerInRangeCorrect(p: seq<int>, start: int, end: int, value: int)
    ensures CountSmallerInRange(p, start, end, value) >= 0
    decreases if start <= end then end - start + 1 else 0
{
    if start > end {
        // Base case: returns 0, which is >= 0
        assert CountSmallerInRange(p, start, end, value) == 0;
    } else if start < 0 || start >= |p| {
        // Base case: returns 0, which is >= 0
        assert CountSmallerInRange(p, start, end, value) == 0;
    } else {
        // Recursive case
        var contribution := if p[start] < value then 1 else 0;
        assert contribution >= 0;
        
        // Prove the recursive call is >= 0
        CountSmallerInRangeCorrect(p, start + 1, end, value);
        assert CountSmallerInRange(p, start + 1, end, value) >= 0;
        
        // Therefore the sum is >= 0
        assert CountSmallerInRange(p, start, end, value) == contribution + CountSmallerInRange(p, start + 1, end, value);
        assert CountSmallerInRange(p, start, end, value) >= 0;
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
    
    result := "";
    var i := 0;
    
    while i < m
        invariant 0 <= i <= m
        invariant |lines| == 2 + m
        invariant |result| >= 0
        invariant forall j :: 0 <= j < |result| ==> result[j] in "YesNo\n"
        invariant i > 0 ==> |result| > 0
        invariant i == 0 ==> result == ""
        invariant var output_lines := SplitLines(result);
                  |output_lines| == i &&
                  (forall k :: 0 <= k < i ==> 
                      var query := ParseIntegers(lines[2 + k]);
                      var l := query[0];
                      var r := query[1];
                      var x := query[2];
                      var px := p[x - 1];
                      var cnt := l + CountSmallerInRange(p, l - 1, r - 1, px);
                      output_lines[k] == (if cnt == x then "Yes" else "No"))
    {
        var query := ParseIntegers(lines[2 + i]);
        var l := query[0];
        var r := query[1];
        var x := query[2];
        var px := p[x - 1];
        
        CountSmallerInRangeCorrect(p, l - 1, r - 1, px);
        var cnt := l + CountSmallerInRange(p, l - 1, r - 1, px);
        
        if cnt == x {
            result := result + "Yes\n";
        } else {
            result := result + "No\n";
        }
        
        i := i + 1;
    }
}
// </vc-code>

