predicate ValidInputFormat(input: string)
{
    |input| > 0 && 
    exists lines: seq<string> ::
        lines == SplitLines(input) &&
        |lines| >= 1 &&
        IsValidInteger(lines[0]) &&
        var t := StringToInt(lines[0]);
        1 <= t <= 100 &&
        |lines| >= 1 + 3*t &&
        forall i :: 0 <= i < t ==> 
            var base_idx := 1 + 3*i;
            base_idx + 2 < |lines| &&
            IsValidString(lines[base_idx]) &&
            IsValidInteger(lines[base_idx + 1]) &&
            IsValidIntegerArray(lines[base_idx + 2]) &&
            var s := lines[base_idx];
            var m := StringToInt(lines[base_idx + 1]);
            var b_array := ParseIntegerArray(lines[base_idx + 2]);
            1 <= |s| <= 50 &&
            (forall j :: 0 <= j < |s| ==> 'a' <= s[j] <= 'z') &&
            1 <= m <= |s| &&
            |b_array| == m &&
            forall k :: 0 <= k < m ==> 0 <= b_array[k] <= 1225
}

predicate ValidOutputFormat(output: string, input: string)
    requires ValidInputFormat(input)
{
    var test_cases := GetTestCases(input);
    |test_cases| > 0 ==> 
    exists output_lines: seq<string> ::
        output_lines == SplitLines(output) &&
        |output_lines| >= |test_cases| &&
        forall i :: 0 <= i < |test_cases| ==> 
            var (s, m, b) := test_cases[i];
            i < |output_lines| &&
            |output_lines[i]| == m &&
            forall j :: 0 <= j < |output_lines[i]| ==> 'a' <= output_lines[i][j] <= 'z'
}

predicate OutputSatisfiesConstraints(output: string, input: string)
    requires ValidInputFormat(input)
{
    var test_cases := GetTestCases(input);
    var output_lines := SplitLines(output);
    |test_cases| > 0 && |output_lines| >= |test_cases| ==>
    forall i :: 0 <= i < |test_cases| ==> 
        var (s, m, b) := test_cases[i];
        i < |output_lines| &&
        var t := output_lines[i];
        |t| == m &&
        (forall j :: 0 <= j < m ==> 
            b[j] == SumDistancesToGreaterChars(t, j))
}

predicate PreservesCharacterUsage(output: string, input: string)
    requires ValidInputFormat(input)
{
    var test_cases := GetTestCases(input);
    var output_lines := SplitLines(output);
    |test_cases| > 0 && |output_lines| >= |test_cases| ==>
    forall i :: 0 <= i < |test_cases| ==> 
        var (s, m, b) := test_cases[i];
        i < |output_lines| &&
        var t := output_lines[i];
        forall c :: 'a' <= c <= 'z' ==> CountChar(t, c) <= CountChar(s, c)
}

predicate ContainsNewlineTerminatedResults(output: string)
{
    |output| > 0 ==> output[|output|-1] == '\n'
}

function SumDistancesToGreaterChars(t: string, j: int): int
    requires 0 <= j < |t|
{
    SumDistancesToGreaterCharsHelper(t, j, 0)
}

function AbsDiff(i: int, j: int): int
    ensures AbsDiff(i, j) >= 0
    ensures AbsDiff(i, j) == if i >= j then i - j else j - i
{
    if i >= j then i - j else j - i
}

// <vc-helpers>
function SumDistancesToGreaterCharsHelper(t: string, j: int, k: int): int
    requires 0 <= j < |t|
    requires 0 <= k <= |t|
    decreases |t| - k
{
    if k >= |t| then 0
    else if t[k] > t[j] then AbsDiff(k, j) + SumDistancesToGreaterCharsHelper(t, j, k+1)
    else SumDistancesToGreaterCharsHelper(t, j, k+1)
}

function CountChar(s: string, c: char): int
    decreases |s|
{
    if |s| == 0 then 0
    else (if s[0] == c then 1 else 0) + CountChar(s[1..], c)
}

function SplitLines(s: string): seq<string>
    ensures |SplitLines(s)| >= 0
{
    if |s| == 0 then []
    else
        var first_line := "";
        var i := 0;
        while i < |s| && s[i] != '\n'
            invariant 0 <= i <= |s|
            invariant |first_line| == i
        {
            first_line := first_line + [s[i]];
            i := i + 1;
        }
        if i < |s| then [first_line] + SplitLines(s[i+1..])
        else [first_line]
}

function IsValidInteger(s: string): bool
{
    |s| > 0 && (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')
}

function StringToInt(s: string): int
    requires IsValidInteger(s)
{
    if |s| == 0 then 0
    else StringToIntHelper(s, 0)
}

function StringToIntHelper(s: string, acc: int): int
    requires |s| >= 0
    decreases |s|
{
    if |s| == 0 then acc
    else StringToIntHelper(s[1..], acc * 10 + (s[0] as int - '0' as int))
}

function IsValidIntegerArray(s: string): bool
{
    |s| > 0 && exists parts: seq<string> :: parts == SplitBySpaces(s) && |parts| > 0 &&
        forall i :: 0 <= i < |parts| ==> IsValidInteger(parts[i])
}

function ParseIntegerArray(s: string): seq<int>
    requires IsValidIntegerArray(s)
{
    var parts := SplitBySpaces(s);
    ParseIntegerArrayHelper(parts, 0)
}

function ParseIntegerArrayHelper(parts: seq<string>, idx: int): seq<int>
    requires 0 <= idx <= |parts|
    decreases |parts| - idx
{
    if idx >= |parts| then []
    else [StringToInt(parts[idx])] + ParseIntegerArrayHelper(parts, idx+1)
}

function SplitBySpaces(s: string): seq<string>
    ensures |SplitBySpaces(s)| >= 0
{
    if |s| == 0 then []
    else
        var first_part := "";
        var i := 0;
        while i < |s| && s[i] != ' '
            invariant 0 <= i <= |s|
            invariant |first_part| == i
        {
            first_part := first_part + [s[i]];
            i := i + 1;
        }
        if i < |s| then [first_part] + SplitBySpaces(s[i+1..])
        else [first_part]
}

function IsValidString(s: string): bool
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}

function GetTestCases(input: string): seq<(string, int, seq<int>)>
    requires ValidInputFormat(input)
{
    var lines := SplitLines(input);
    var t := StringToInt(lines[0]);
    GetTestCasesHelper(lines, t, 0)
}

function GetTestCasesHelper(lines: seq<string>, t: int, i: int): seq<(string, int, seq<int>)>
    requires 0 <= i <= t
    decreases t - i
{
    if i >= t then []
    else
        var base_idx := 1 + 3*i;
        var s := lines[base_idx];
        var m := StringToInt(lines[base_idx + 1]);
        var b_array := ParseIntegerArray(lines[base_idx + 2]);
        [(s, m, b_array)] + GetTestCasesHelper(lines, t, i+1)
}

lemma SumDistancesToGreaterCharsCorrect(t: string, j: int)
    requires 0 <= j < |t|
    ensures SumDistancesToGreaterChars(t, j) ==
        sum k | 0 <= k < |t| && t[k] > t[j] :: AbsDiff(k, j)
{
}

lemma CountCharCorrect(s: string, c: char)
    ensures CountChar(s, c) == |set j | 0 <= j < |s| && s[j] == c|
{
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires ValidInputFormat(stdin_input)
    ensures ValidOutputFormat(result, stdin_input)
    ensures OutputSatisfiesConstraints(result, stdin_input)
    ensures PreservesCharacterUsage(result, stdin_input)
    ensures result != "" ==> ContainsNewlineTerminatedResults(result)
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(stdin_input);
    var t := StringToInt(lines[0]);
    var result_lines: seq<string> := [];
    var i := 0;
    
    while i < t
        invariant 0 <= i <= t
        invariant |result_lines| == i
    {
        var base_idx := 1 + 3*i;
        var s := lines[base_idx];
        var m := StringToInt(lines[base_idx + 1]);
        var b := ParseIntegerArray(lines[base_idx + 2]);
        
        var t_string := "";
        var char_count: map<char, int> := map[];
        var c := 'a';
        while c <= 'z'
            invariant 'a' <= c <= 'z' + 1
            invariant forall ch :: 'a' <= ch <= 'z' ==> char_count.Contains(ch)
        {
            char_count := char_count[c := 0];
            c := (c as int + 1) as char;
        }
        
        var j := 0;
        while j < |s|
            invariant 0 <= j <= |s|
            invariant forall ch :: 'a' <= ch <= 'z' ==> char_count[ch] == CountChar(s[0..j], ch)
        {
            char_count := char_count[s[j] := char_count[s[j]] + 1];
            j := j + 1;
        }
        
        var result_chars: seq<char> := [];
        var pos := 0;
        while pos < m
            invariant 0 <= pos <= m
            invariant |result_chars| == pos
        {
            var c := 'z';
            while c >= 'a'
                invariant 'a' - 1 <= c <= 'z'
                decreases c
            {
                if char_count[c] > 0 {
                    var temp_result := result_chars + [c];
                    var temp_string := seq(|temp_result|, k requires 0 <= k < |temp_result| => temp_result[k]);
                    
                    var valid := true;
                    var k := 0;
                    while k < pos
                        invariant 0 <= k <= pos
                    {
                        if temp_string[k] > c {
                            var expected_dist := AbsDiff(k, pos);
                            var actual_dist := AbsDiff(k, pos);
                            if expected_dist != b[k] {
                                valid := false;
                            }
                        }
                        k := k + 1;
                    }
                    
                    if valid {
                        result_chars := result_chars + [c];
                        char_count := char_count[c := char_count[c] - 1];
                        break;
                    }
                }
                c := (c as int - 1) as char;
            }
            pos := pos + 1;
        }
        
        var result_string := seq(|result_chars|, j requires 0 <= j < |result_chars| => result_chars[j]);
        result_lines := result_lines + [result_string];
        i := i + 1;
    }
    
    result := "";
    i := 0;
    while i < |result_lines|
        invariant 0 <= i <= |result_lines|
    {
        result := result + result_lines[i] + "\n";
        i := i + 1;
    }
}
// </vc-code>

