function split_lines(s: string): seq<string>
{
    [""]  // placeholder implementation
}

function is_valid_number(s: string): bool
{
    true  // placeholder implementation
}

function parse_int(s: string): int
    requires is_valid_number(s)
{
    0  // placeholder implementation
}

function is_binary_string(s: string): bool
{
    true  // placeholder implementation
}

function ends_with_newline(s: string): bool
{
    |s| > 0 && s[|s|-1] == '\n'
}

predicate ValidInput(input: string)
{
    |input| > 0 &&
    input[|input|-1] == '\n' &&
    exists lines :: 
        lines == split_lines(input) &&
        |lines| >= 2 &&
        is_valid_number(lines[0]) &&
        var t := parse_int(lines[0]);
        t >= 1 && t <= 100 &&
        |lines| == t + 1 &&
        forall i :: 1 <= i < |lines| ==> 
            is_binary_string(lines[i]) && |lines[i]| >= 1 && |lines[i]| <= 1000
}

predicate ValidOutput(result: string)
{
    result != "" &&
    (ends_with_newline(result) || result == "") &&
    exists output_lines :: 
        output_lines == split_lines(result) &&
        |output_lines| >= 1 &&
        (forall i :: 0 <= i < |output_lines|-1 ==> is_valid_number(output_lines[i])) &&
        (forall i :: 0 <= i < |output_lines|-1 ==> parse_int(output_lines[i]) >= 0)
}

predicate CorrectResult(input: string, result: string)
    requires ValidInput(input)
{
    exists input_lines, t :: 
        input_lines == split_lines(input) &&
        t == parse_int(input_lines[0]) &&
        var output_lines := split_lines(result);
        |output_lines| == t + 1 &&
        forall test_case :: 0 <= test_case < t ==>
            var s := input_lines[test_case + 1];
            var min_ops := parse_int(output_lines[test_case]);
            min_ops == min_operations_to_make_good(s)
}

function min_operations_to_make_good(s: string): int
    requires is_binary_string(s)
    ensures min_operations_to_make_good(s) >= 0
    ensures min_operations_to_make_good(s) <= |s|
{
    if |s| == 0 then 0
    else min_ops_helper(s, 0, |s|)
}

// <vc-helpers>
function split_lines_helper(s: string, index: nat): (lines: seq<string>)
    requires index <= |s|
    ensures |lines| == if index == |s| then 0 else (if s[index..] == "" then 0 else |split_lines(s[index..])|)
{
    if index == |s| then []
    else
        var i := index;
        var lines := [];
        while i < |s| && s[i] != '\n'
            invariant index <= i <= |s|
            invariant lines == []
        {
            i := i + 1;
        }
        var line := s[index..i];
        var next_index := if i < |s| then i + 1 else i;
        lines := [line] + split_lines_helper(s, next_index);
}

function min_ops_helper(s: string, start: nat, end: nat): int
    requires 0 <= start <= end <= |s|
    requires is_binary_string(s)
    ensures min_ops_helper(s, start, end) >= 0
    ensures min_ops_helper(s, start, end) <= end - start
{
    if start >= end then 0
    else
        var first := s[start];
        if end - start == 1 then 0
        else
            var result := min_ops_helper(s, start + 1, end);
            if first != s[start + 1] then
                result := min(result + 1, (end - start - 1) - result)
            else
                result
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(result)
    ensures CorrectResult(input, result)
// </vc-spec>
// <vc-code>
{
    var input_lines := split_lines(input);
    var t := parse_int(input_lines[0]);
    var result_lines := [];
    var i := 1;
    while i <= t
        invariant 1 <= i <= t + 1
        invariant result_lines == seq j | 0 <= j < i-1 :: parse_int(input_lines[j+1]).ToString()
    {
        var s := input_lines[i];
        var min_ops := min_operations_to_make_good(s);
        result_lines := result_lines + [min_ops.ToString()];
        i := i + 1;
    }
    var result := "";
    i := 0;
    while i < |result_lines|
        invariant 0 <= i <= |result_lines|
        invariant result == concat_lines(result_lines[..i])
    {
        if i > 0 then
            result := result + "\n";
        result := result + result_lines[i];
        i := i + 1;
    }
    result
}
// </vc-code>

