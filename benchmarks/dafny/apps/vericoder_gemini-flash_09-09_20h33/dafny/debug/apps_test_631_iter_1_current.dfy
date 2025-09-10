predicate valid_input_format(s: string)
{
    |s| >= 7 && 
    exists pos :: 0 < pos < |s| && s[pos] == '\n'
}

function get_test_count(stdin_input: string): int
    requires valid_input_format(stdin_input)
    ensures get_test_count(stdin_input) >= 1
{
    1
}

function get_array_sum(stdin_input: string, test_idx: int): int
    requires valid_input_format(stdin_input)
    requires 0 <= test_idx < get_test_count(stdin_input)
{
    0
}

function get_target_m(stdin_input: string, test_idx: int): int
    requires valid_input_format(stdin_input)
    requires 0 <= test_idx < get_test_count(stdin_input)
{
    0
}

function expected_output_for_input(stdin_input: string): string
    requires valid_input_format(stdin_input)
{
    compute_expected_output(stdin_input, 0, get_test_count(stdin_input))
}

predicate behavioral_correctness(stdin_input: string, result: string)
    requires valid_input_format(stdin_input)
{
    var T := get_test_count(stdin_input);
    count_responses(result) == T &&
    (forall i :: 0 <= i < T ==>
        var array_sum := get_array_sum(stdin_input, i);
        var target_m := get_target_m(stdin_input, i);
        var response := get_response_at_index(result, i);
        (array_sum == target_m <==> response == "YES\n") &&
        (array_sum != target_m <==> response == "NO\n"))
}

// <vc-helpers>
function compute_expected_output(stdin_input: string, k: int, T: int): string
    requires valid_input_format(stdin_input)
    requires 0 <= k <= T
    ensures var res := compute_expected_output(stdin_input, k, T);
            (res == "" <==> k == T)
{
    if k == T then
        ""
    else
        var array_sum := get_array_sum(stdin_input, k);
        var target_m := get_target_m(stdin_input, k);
        var response := if array_sum == target_m then "YES\n" else "NO\n";
        response + compute_expected_output(stdin_input, k + 1, T)
}

function count_responses(s: string): int
    decreases |s|
{
    if s == "" then
        0
    else if "\n" in s then
        var newline_pos := s.IndexOf('\n');
        // Ensure newline_pos is valid, although IndexOf should handle it if '\n' is in s
        if newline_pos >= 0 then
            1 + count_responses(s[newline_pos + 1 ..])
        else
            0 // Should not happen if '\n' is in s
    else
        0
}

function get_response_at_index(s: string, index: int): string
    requires index >= 0
    requires count_responses(s) > index
    decreases index
{
    if index == 0 then
        var newline_pos := s.IndexOf('\n');
        s[0 .. newline_pos + 1]
    else
        var newline_pos := s.IndexOf('\n');
        get_response_at_index(s[newline_pos + 1 ..], index - 1)
}


predicate is_digit(c: char) { '0' <= c <= '9' }

function parse_int(s: string): (i: int)
    requires forall c :: c in s ==> is_digit(c)
    requires |s| > 0
    ensures is_digit_string(s) ==> i >= 0
    ensures (s == "0") ==> (i == 0)
    ensures (s == "1") ==> (i == 1)
{
    var num := 0;
    for k := 0 to |s|
        invariant 0 <= k <= |s|
        invariant num >= 0
        invariant num == to_int_from_chars(s[0..k])
    {
        if k < |s| {
            num := num * 10 + (s[k] - '0');
        }
    }
    return num;
}

function to_int_from_chars(chars: seq<char>): int
    requires forall c :: c in chars ==> is_digit(c)
    requires |chars| > 0
    ensures to_int_from_chars(chars) >= 0
{
    if |chars| == 1 then
        (chars[0] - '0')
    else chars[0] - '0' * (10 * (|chars| - 1)) + to_int_from_chars(chars[1..]) // Simplified version for Dafny
}

predicate is_digit_string(s: string) {
    forall c :: c in s ==> is_digit(c)
}

function find_nth_newline(s: string, n: int): int
    requires n >= 0
    requires n == 0 ==> s.IndexOf('\n') >= 0 || n > 0 ==> count_responses(s) >= n
    ensures var idx := find_nth_newline(s, n);
            (idx == -1 && count_responses(s) < n) || (idx >= 0 && n > 0 && s[idx] == '\n')
            
{
    var current_pos := 0;
    var count := 0;
    while count < n
        invariant 0 <= count <= n
        invariant current_pos >= 0
        invariant count_responses(s[current_pos..]) >= n - count
        invariant (count > 0 ==> current_pos > 0 && s[current_pos-1] == '\n') || (count == 0 && current_pos == 0)
        decreases n - count
    {
        var next_newline_idx := s.IndexOf('\n', current_pos);
        if next_newline_idx == -1 then
            return -1; // Not enough newlines
        current_pos := next_newline_idx + 1;
        count := count + 1;
    }
    return current_pos - 1; // Return the position of the n-th newline character
}


function extract_test_line(s: string, test_idx: int): string
    requires count_responses(s) > test_idx
    ensures var line := extract_test_line(s, test_idx);
            line.IndexOf('\n') == |line| - 1
            line.IndexOf('\n') >= 0
{
    var start_idx := 0;
    if test_idx > 0 {
        start_idx := find_nth_newline(s, test_idx) + 1;
    }
    var end_idx := s.IndexOf('\n', start_idx);
    s[start_idx .. end_idx + 1]
}

function get_test_count_full(stdin_input: string): int
    requires valid_input_format(stdin_input)
    ensures get_test_count_full(stdin_input) >= 1
{
    var newline_pos := stdin_input.IndexOf('\n');
    var T_str := stdin_input[0 .. newline_pos];
    // This requires proving T_str is digits, which is implicitly assumed by parse_int.
    // For now, satisfy the postcondition.
    var T_val := parse_int(T_str);
    if T_val >= 1 then T_val else 1 // Ensure >= 1 due to function postcondition
}

function get_array_sum_full(stdin_input: string, test_idx: int): int
    requires valid_input_format(stdin_input)
    requires 0 <= test_idx < get_test_count_full(stdin_input)
    ensures get_array_sum_full(stdin_input, test_idx) >= 0
{
    var T_line_end_idx := stdin_input.IndexOf('\n');
    var current_line_start := T_line_end_idx + 1;

    // Skip N lines (test_idx * 2) after the T line.
    // Each test consists of an array line and a target M line.
    for i := 0 to test_idx * 2
        invariant 0 <= i <= test_idx * 2
        invariant current_line_start >= 0
        invariant count_responses(stdin_input[T_line_end_idx+1..]) >= i
        decreases test_idx * 2 - i
    {
        var next_newline_idx := stdin_input.IndexOf('\n', current_line_start);
        if next_newline_idx == -1 then return 0; // Should not happen given preconditions
        current_line_start := next_newline_idx + 1;
    }

    // current_line_start is now the start of the array line for test_idx
    var array_line_end_idx := stdin_input.IndexOf('\n', current_line_start);
    if array_line_end_idx == -1 then return 0; // Should not happen
    var array_str := stdin_input[current_line_start .. array_line_end_idx];

    var sum := 0;
    var start_char_idx := 0;
    while start_char_idx < |array_str|
        invariant 0 <= start_char_idx <= |array_str|
        invariant sum >= 0
        decreases |array_str| - start_char_idx
    {
        var space_idx := array_str.IndexOf(' ', start_char_idx);
        var num_str: string;
        if space_idx == -1 then
            num_str := array_str[start_char_idx ..];
            start_char_idx := |array_str|;
        else
            num_str := array_str[start_char_idx .. space_idx];
            start_char_idx := space_idx + 1;
        sum := sum + parse_int(num_str);
    }
    sum
}

function get_target_m_full(stdin_input: string, test_idx: int): int
    requires valid_input_format(stdin_input)
    requires 0 <= test_idx < get_test_count_full(stdin_input)
    ensures get_target_m_full(stdin_input, test_idx) >= 0
{
    var T_line_end_idx := stdin_input.IndexOf('\n');
    var current_line_start := T_line_end_idx + 1;

    // Skip N lines (test_idx * 2 + 1) after the T line.
    // +1 because we want to skip the array line as well.
    for i := 0 to test_idx * 2 + 1
        invariant 0 <= i <= test_idx * 2 + 1
        invariant current_line_start >= 0
        invariant count_responses(stdin_input[T_line_end_idx+1..]) >= i
        decreases test_idx * 2 + 1 - i
    {
        var next_newline_idx := stdin_input.IndexOf('\n', current_line_start);
        if next_newline_idx == -1 then return 0; // Should not happen given preconditions
        current_line_start := next_newline_idx + 1;
    }

    // current_line_start is now the start of the target M line for test_idx
    var m_line_end_idx := stdin_input.IndexOf('\n', current_line_start);
    if m_line_end_idx == -1 then return 0; // Should not happen
    var m_str := stdin_input[current_line_start .. m_line_end_idx];
    parse_int(m_str)
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires valid_input_format(stdin_input)
    requires |stdin_input| > 0
    requires stdin_input != ""
    requires '\n' in stdin_input
    requires exists pos :: 0 <= pos < |stdin_input| && stdin_input[pos] == '\n'
    requires forall i :: 0 <= i < |stdin_input| ==> 
        stdin_input[i] in
// </vc-spec>
// <vc-code>
{
    var T := get_test_count_full(stdin_input);
    var res := "";
    for i := 0 to T
        invariant 0 <= i <= T
        invariant T == get_test_count_full(stdin_input)
        invariant res == compute_expected_output(stdin_input, 0, i)
        decreases T - i
    {
        if i < T {
            var array_sum := get_array_sum_full(stdin_input, i);
            var target_m := get_target_m_full(stdin_input, i);
            if array_sum == target_m {
                res := res + "YES\n";
            } else {
                res := res + "NO\n";
            }
        }
    }
    return res;
}
// </vc-code>

