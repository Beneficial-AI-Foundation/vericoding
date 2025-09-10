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
function min_ops_helper(s: string, start: int, end: int): int
    requires 0 <= start <= end <= |s|
    requires is_binary_string(s)
    ensures min_ops_helper(s, start, end) >= 0
    ensures min_ops_helper(s, start, end) <= end - start
    decreases end - start
{
    if start >= end then 0
    else if start + 1 >= end then 0
    else if s[start] == s[start + 1] then
        1 + min_ops_helper(s, start + 1, end)
    else
        min_ops_helper(s, start + 1, end)
}

function string_of_int(n: int): string
    requires n >= 0
{
    if n == 0 then "0"
    else if n < 10 then [('0' as int + n) as char]
    else string_of_int(n / 10) + [('0' as int + (n % 10)) as char]
}

function join_with_newlines(lines: seq<string>): string
{
    if |lines| == 0 then ""
    else if |lines| == 1 then lines[0] + "\n"
    else lines[0] + "\n" + join_with_newlines(lines[1..])
}

lemma min_ops_helper_correctness(s: string, start: int, end: int)
    requires 0 <= start <= end <= |s|
    requires is_binary_string(s)
    ensures min_ops_helper(s, start, end) >= 0
    ensures min_ops_helper(s, start, end) <= end - start
{
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
    var output_lines: seq<string> := [];
    
    var i := 0;
    while i < t
        invariant 0 <= i <= t
        invariant |output_lines| == i
        invariant forall j :: 0 <= j < i ==> is_valid_number(output_lines[j])
        invariant forall j :: 0 <= j < i ==> parse_int(output_lines[j]) >= 0
    {
        var binary_string := input_lines[i + 1];
        var min_ops := min_operations_to_make_good(binary_string);
        var min_ops_str := string_of_int(min_ops);
        output_lines := output_lines + [min_ops_str];
        i := i + 1;
    }
    
    result := join_with_newlines(output_lines);
}
// </vc-code>

