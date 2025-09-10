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
function split_lines(s: string): seq<string>
{
    var lines: seq<string> := [];
    var i := 0;
    while i < |s|
    {
        var j := i;
        while j < |s| && s[j] != '\n'
        {
            j := j + 1;
        }
        lines := lines + [s[i..j]];
        if j < |s|
        {
            i := j + 1;
        }
        else
        {
            i := |s|;
        }
    }
    if ends_with_newline(s)
    {
        lines := lines + [""];
    }
    lines
}

function is_valid_number(s: string): bool
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function parse_int(s: string): int
    requires is_valid_number(s)
{
    var num := 0;
    for i := 0 to |s| - 1
    {
        num := num * 10 + (s[i] - '0');
    }
    num
}

function is_binary_string(s: string): bool
{
    forall i :: 0 <= i < |s| ==> s[i] == '0' || s[i] == '1'
}

function min_operations_to_make_good(s: string): int
    requires is_binary_string(s)
    ensures min_operations_to_make_good(s) >= 0
    ensures min_operations_to_make_good(s) <= |s|
{
    var count0 := 0;
    var count1 := 0;
    for i := 0 to |s|-1
    {
        var expected0 := if i % 2 == 0 then '0' else '1';
        var expected1 := if i % 2 == 0 then '1' else '0';
        if s[i] != expected0 { count0 := count0 + 1; }
        if s[i] != expected1 { count1 := count1 + 1; }
    }
    if count0 < count1 then count0 else count1
}

function int_to_string(x: int): string
    requires x >= 0
{
    if x == 0 then "0"
    else
        var s := "";
        var n := x;
        while n > 0
            invariant n >= 0
        {
            s := char('0' + (n % 10)) + s;
            n := n / 10;
        }
        s
}

function join_lines(lines: seq<string>): string
{
    var result := "";
    for i := 0 to |lines|-1
    {
        if i > 0
        {
            result := result + "\n";
        }
        result := result + lines[i];
    }
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
    var output_lines: seq<string> := [];
    for i := 0 to t - 1
    {
        var s := input_lines[i + 1];
        var ops := min_operations_to_make_good(s);
        var str_ops := int_to_string(ops);
        output_lines := output_lines + [str_ops];
    }
    var result_str := join_lines(output_lines) + "\n";
    result := result_str;
}
// </vc-code>

