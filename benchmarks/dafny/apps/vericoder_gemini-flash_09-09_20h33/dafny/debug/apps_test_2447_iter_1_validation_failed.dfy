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
    if s == "" then
      []
    else if s.Contains('\n') then
      var i := s.IndexOf('\n');
      var head := s.Substring(0, i);
      var tail := s.Substring(i + 1);
      [head] + split_lines(tail)
    else
      [s]
}

function is_valid_number(s: string): bool
{
    if s == "" then false
    else if exists i :: 0 <= i < |s| && !(s[i] in ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']) then false
    else true
}

function parse_int(s: string): int
    requires is_valid_number(s)
{
    if s == "" then 0
    else (s[0] as int - '0' as int) + 10 * parse_int(s[1..])
}

function is_binary_string(s: string): bool
{
    forall i :: 0 <= i < |s| ==> (s[i] == '0' || s[i] == '1')
}

function min_ops_helper(s: string, start: nat, end_excl: nat): int
    requires 0 <= start <= end_excl <= |s|
    requires forall i :: start <= i < end_excl ==> (s[i] == '0' || s[i] == '1')
    ensures 0 <= min_ops_helper(s, start, end_excl) <= (end_excl - start)
{
    if start == end_excl then 0
    else
        var current_len := end_excl - start;
        var s_sub := s.Substring(start, current_len);
        var ones := 0;
        var zeros := 0;
        for i := 0 to current_len - 1
            invariant 0 <= i <= current_len
            invariant ones == count_char(s_sub, '1', 0, i)
            invariant zeros == count_char(s_sub, '0', 0, i)
        {
            if s_sub[i] == '1' then ones := ones + 1;
            else zeros := zeros + 1;
        }

        min(ones, zeros)
}

function count_char(s: string, c: char, start: nat, end_excl: nat): nat
    requires 0 <= start <= end_excl <= |s|
    ensures count_char(s, c, start, end_excl) <= (end_excl - start)
{
    if start == end_excl then 0
    else
        var rest := count_char(s, c, start + 1, end_excl);
        if s[start] == c then 1 + rest
        else rest
}

function min(a: int, b: int): int { if a < b then a else b }

function get_min_operations(s: string): int
    requires is_binary_string(s)
    ensures get_min_operations(s) >= 0
    ensures get_min_operations(s) <= |s|
{
    if |s| == 0 then 0
    else min_ops_helper(s, 0, |s|)
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
    var output_accumulator: seq<string> := [];

    var i := 0;
    while i < t
        invariant 0 <= i <= t
        invariant |output_accumulator| == i
        invariant forall k :: 0 <= k < i ==> 
            is_valid_number(output_accumulator[k]) && parse_int(output_accumulator[k]) == get_min_operations(input_lines[k+1])
    {
        var s := input_lines[i + 1];
        var min_ops := get_min_operations(s);
        output_accumulator := output_accumulator + [min_ops as string];
        i := i + 1;
    }

    // Add a trailing newline character to match the `ends_with_newline` requirement in `ValidOutput`
    // However, the `CorrectResult` predicate compares the split lines, so the newline character
    // is not part of the actual data, but a format requirement.
    // The problem statement implies each test case result is a line, and the last line is the result of the last case.
    // The output should be a sequence of lines. The last line should also be terminated by a newline.
    // Dafny's string.Join takes a separator. If the separator is "\n", it joins with newlines
    // and naturally doesn't add a trailing newline if there are elements. If we need a trailing newline,
    // we must add it manually or join with an empty element at end.

    result := "";
    if |output_accumulator| > 0 {
      result := string.Join("\n", output_accumulator) + "\n";
    }

    // The provided `min_operations_to_make_good` function definition in the template
    // uses `min_ops_helper` which assumes a `start` and `end_excl` which seems
    // to calculate operations for a subsegment. The problem setup suggests it is for
    // the whole string `s`. So `min_ops_helper(s, 0, |s|)` is effectively `get_min_operations(s)`.
    // We replace `min_operations_to_make_good` with `get_min_operations` for clarity
    // and to avoid confusion for the overall logic.

    // Dafny doesn't directly allow function redefinition within the same module,
    // so we assume `min_operations_to_make_good` from the original problem description
    // is implemented as our `get_min_operations`.
}
// </vc-code>

