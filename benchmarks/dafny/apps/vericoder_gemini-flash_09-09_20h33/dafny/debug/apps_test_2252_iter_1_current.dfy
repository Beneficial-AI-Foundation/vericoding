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
function ParseIntegers(line: string): seq<int>
    reads Set.Empty
{
    var numbers := new int[0];
    var i := 0;
    while i < |line|
        invariant 0 <= i <= |line|
        invariant forall k :: 0 <= k < |numbers| ==> numbers[k] >= 0 // Assuming non-negative integers
        // No explicit invariant needed for `numbers`'s relationship to string
    {
        while i < |line| && line[i] == ' '
        {
            i := i + 1;
        }
        if i < |line|
        {
            var j := i;
            while j < |line| && '0' <= line[j] <= '9'
            {
                j := j + 1;
            }
            if j > i
            {
                var num_str := line[i..j];
                var num := 0;
                var p := 1;
                var k := j - 1;
                while k >= i
                    invariant i - 1 <= k < j
                    invariant num == (if k == j - 1 then 0 else (NumFromString(line[k+1..j])))
                    invariant p == (if k == j - 1 then 1 else Power(10, j - (k+1)))
                {
                    num := num + ( (line[k] - '0') * p );
                    p := p * 10;
                    k := k - 1;
                }
                numbers := numbers + [num];
            }
            i := j;
        }
    }
    return numbers
}

function NumFromString(s: string): int
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    reads Set.Empty
{
    var num := 0;
    var p := 1;
    var k := |s| - 1;
    while k >= 0
        invariant -1 <= k < |s|
        invariant num == (if k == |s| - 1 then 0 else NumFromStringAux(s[k+1..|s|]))
        invariant p == (if k == |s| - 1 then 1 else Power(10, |s| - (k+1)))
    {
        num := num + ( (s[k] - '0') * p );
        p := p * 10;
        k := k - 1;
    }
    return num
}

function NumFromStringAux(s: string): int
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    reads Set.Empty
{
    if |s| == 0 then 0
    else (s[0] - '0') * Power(10, |s|-1) + NumFromStringAux(s[1..])
}

function Power(base: int, exp: nat): int
    reads Set.Empty
{
    if exp == 0 then 1
    else base * Power(base, exp - 1)
}


predicate IsValidPermutation(p: seq<int>, n: int)
{
    |p| == n && 
    (forall i :: 0 <= i < |p| ==> 1 <= p[i] <= n) &&
    (forall i, j :: 0 <= i < j < |p| ==> p[i] != p[j])
}

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
        var query := ParseInteters(lines[i]);
        |query| == 3 &&
        var l := query[0];
        var r := query[1];
        var x := query[2];
        1 <= l <= x <= r <= n)
}

function CountSmallerInRange(p: seq<int>, start: int, end: int, value: int): int
    decreases if start <= end then end - start + 1 else 0
{
    if start > end then 0
    else if start < 0 || start >= |p| then 0
    else (if p[start] < value then 1 else 0) + CountSmallerInRange(p, start + 1, end, value)
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
    var input_lines := SplitLines(stdin_input);
    var first_line := ParseIntegers(input_lines[0]);
    var n := first_line[0];
    var m := first_line[1];
    var p := ParseIntegers(input_lines[1]);

    var results: seq<string> := [];
    var i := 0;
    while i < m
        invariant 0 <= i <= m
        invariant |results| == i
        invariant forall k :: 0 <= k < i ==> (results[k] == "Yes" || results[k] == "No")
    {
        var query_line := input_lines[2 + i];
        var query := ParseIntegers(query_line);
        var l := query[0];
        var r := query[1];
        var x := query[2];

        var px := p[x - 1];
        var count_smaller := CountSmallerInRange(p, l - 1, r - 1, px);
        var cnt := l + count_smaller;

        if cnt == x {
            results := results + ["Yes"];
        } else {
            results := results + ["No"];
        }
        i := i + 1;
    }

    result := "";
    if |results| > 0 {
        var j := 0;
        while j < |results|
            invariant 0 <= j <= |results|
            invariant result == (if j == 0 then "" else (ConcatenateWithNewline(results[0..j])))
        {
            result := result + results[j];
            if j < |results| - 1 {
                result := result + "\n";
            }
            j := j + 1;
        }
        result := result + "\n";
    }
    return result;
}
// </vc-code>

