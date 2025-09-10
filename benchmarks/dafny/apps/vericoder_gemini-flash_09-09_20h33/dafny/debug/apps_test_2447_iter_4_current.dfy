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
    requires forall i :: start <= i < end ==> (s[i] == '0' || s[i] == '1')
    ensures min_ops_helper(s, start, end) >= 0
    ensures min_ops_helper(s, start, end) <= end - start
{
    if start == end then 0
    else if start + 1 == end then 0 // Single character string is always "good"
    else
        var num_zeros := count_char(s, '0', start, end);
        var num_ones := count_char(s, '1', start, end);
        
        var min_operations := num_zeros; // Cost to make all '1's
        if num_ones < min_operations then min_operations := num_ones; // Cost to make all '0's

        var current_zeros := 0;
        var current_ones := 0;
        for i := start to end-1
            invariant start <= i <= end
            invariant current_zeros == count_char(s, '0', start, i)
            invariant current_ones == count_char(s, '1', start, i)
            invariant min_operations >= 0 && min_operations <= end - start
        {
            if s[i] == '0' then current_zeros := current_zeros + 1;
            else current_ones := current_ones + 1;

            // Consider a split point after index i
            // Left part: s[start..i], right part: s[i+1..end-1]
            var left_len := (i - start) + 1;
            if left_len > 0 && left_len < end - start {
                var right_zeros := count_char(s, '0', i + 1, end);
                var right_ones := count_char(s, '1', i + 1, end);

                var cost1 := current_ones + right_zeros; // left all 0s, right all 1s
                var cost2 := current_zeros + right_ones; // left all 1s, right all 0s
                
                var current_split_ops := cost1;
                if cost2 < current_split_ops then current_split_ops := cost2;
               
                if current_split_ops < min_operations then min_operations := current_split_ops;
            }
        }
        min_operations
}

function count_char(s: string, c: char, start: int, end: int): int
    requires 0 <= start <= end <= |s|
    ensures count_char(s, c, start, end) >= 0
    ensures count_char(s, c, start, end) <= end - start
{
    var count := 0;
    for i := start to end-1
        invariant start <= i <= end
        invariant count == count_char(s, c, start, i)
    {
        if s[i] == c then count := count + 1;
    }
    return count;
}

function calculate_min_ops(left_zeros: int, left_ones: int, s: string, total_start: int, current_i: int, total_end: int): int
    requires 0 <= total_start <= current_i < total_end
    requires left_zeros == count_char(s, '0', total_start, current_i + 1)
    requires left_ones == count_char(s, '1', total_start, current_i + 1)
    requires forall k :: total_start <= k < total_end ==> (s[k] == '0' || s[k] == '1')
{
    var right_start := current_i + 1;
    var right_zeros := count_char(s, '0', right_start, total_end);
    var right_ones := count_char(s, '1', right_start, total_end);

    var cost_left_all_0s := left_ones;
    var cost_left_all_1s := left_zeros;

    var cost_right_all_0s := right_ones;
    var cost_right_all_1s := right_zeros;

    var current_min_ops := cost_left_all_0s + cost_right_all_1s; // left 0s, right 1s
    if cost_left_all_1s + cost_right_all_0s < current_min_ops then current_min_ops := cost_left_all_1s + cost_right_all_0s; // left 1s, right 0s
    
    current_min_ops
}

function parse_int_with_newline_check(s: string): int
    requires is_valid_number(s)
    ensures parse_int_with_newline_check(s) == parse_int(s)
{
    if |s| > 0 && s[|s|-1] == '\n' then
        parse_int(s[..|s|-1])
    else
        parse_int(s)
}

function min_ops(s: string): int
    requires is_binary_string(s)
    ensures min_ops(s) >= 0
    ensures min_ops(s) <= |s|
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
    var t := parse_int_with_newline_check(input_lines[0]);
    var output_accumulator := new string[t];
    var current_output_index := 0;

    while current_output_index < t
        invariant 0 <= current_output_index <= t
        invariant forall i :: 0 <= i < current_output_index ==>
            var s_i := input_lines[i + 1];
            output_accumulator[i] == (min_ops(s_i) as string)
    {
        var s := input_lines[current_output_index + 1];
        var ops := min_ops(s);
        output_accumulator[current_output_index] := ops as string;
        current_output_index := current_output_index + 1;
    }

    result := "";
    for i := 0 to t - 1
        invariant 0 <= i <= t
        invariant result == (if i == 0 then "" else (result + output_accumulator[i-1] + "\n"))
        invariant (if i==0 then result == "" else forall k :: 0 <= k < i ==> is_valid_number(split_lines(result)[k]) && parse_int(split_lines(result)[k]) == min_ops(input_lines[k+1]))
        invariant forall k :: 0 <= k < i ==> ends_with_newline(split_lines(result)[k]) || (k == i-1 && !ends_with_newline(split_lines(result)[k])) // Added last case due to final newline
    {
        result := result + output_accumulator[i] + "\n";
    }
}
// </vc-code>

