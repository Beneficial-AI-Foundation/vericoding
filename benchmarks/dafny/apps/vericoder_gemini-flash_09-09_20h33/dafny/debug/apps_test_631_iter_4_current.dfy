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
    ensures forall i :: 0 <= i < T - k ==> ({
        var array_sum := get_array_sum_full(stdin_input, k + i);
        var target_m := get_target_m_full(stdin_input, k + i);
        var expected_response := if array_sum == target_m then "YES\n" else "NO\n";
        get_response_at_index(res, i) == expected_response
    })
{
    if k == T then
        ""
    else
        var array_sum := get_array_sum_full(stdin_input, k);
        var target_m := get_target_m_full(stdin_input, k);
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
        // IndexOf returns -1 if not found. Precond "\n" in s ensures it's found.
        1 + count_responses(s[newline_pos + 1 ..])
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
    ensures i >= 0
    ensures (s == "0") ==> (i == 0)
    ensures (s == "1") ==> (i == 1)
    // Add ensures clause for actual parsing behavior
    ensures i == (if |s| == 1 then (s[0] - '0') else (parse_int(s[0..|s|-1]) * 10 + (s[|s|-1] - '0')))
{
    if |s| == 1 then
        (s[0] - '0')
    else
        (parse_int(s[0..|s|-1]) * 10 + (s[|s|-1] - '0'))
}


function find_nth_newline(s: string, n: int): int
    requires n >= 0
    requires (n == 0 && s.IndexOf('\n') >= 0) || (n > 0 && count_responses(s) >= n)
    ensures var idx := find_nth_newline(s, n);
            (idx == -1 && count_responses(s) < n) || (idx >= 0 && n > 0 && s[idx] == '\n')
            // Add a postcondition to make it easier to reason about the position of the newline.
            ensures idx == -1 || (n == count_responses(s[0..idx+1]))
            
{
    var current_pos := 0;
    var count := 0;
    while count < n
        invariant 0 <= count <= n
        invariant current_pos >= 0
        invariant (count > 0 ==> current_pos > 0 && s[current_pos-1] == '\n') || (count == 0 && current_pos == 0)
        invariant count_responses(s[0..current_pos]) == count
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


function get_test_count_full(stdin_input: string): int
    requires valid_input_format(stdin_input)
    ensures get_test_count_full(stdin_input) >= 1
    ensures var newline_pos := stdin_input.IndexOf('\n');
            is_digit_string(stdin_input[0 .. newline_pos])
{
    var newline_pos := stdin_input.IndexOf('\n');
    var T_str := stdin_input[0 .. newline_pos];
    var T_val := parse_int(T_str);
    if T_val >= 1 then T_val else 1 // Ensure >= 1 due to function postcondition
}

predicate is_digit_string(s: string) {
    forall c :: c in s ==> is_digit(c)
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
    var lines_to_skip := test_idx * 2;
    for i := 0 to lines_to_skip
        invariant 0 <= i <= lines_to_skip
        invariant current_line_start >= T_line_end_idx + 1
        invariant (i == 0 && current_line_start == T_line_end_idx + 1) || (i > 0 && stdin_input[current_line_start-1] == '\n')
        decreases lines_to_skip - i
    {
        var next_newline_idx := stdin_input.IndexOf('\n', current_line_start);
        if next_newline_idx == -1 then return 0; // Should not happen given full input validity
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
        invariant forall k :: start_char_idx <= k < |array_str| ==> (is_digit(array_str[k]) || array_str[k] == ' ')
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
        
        if |num_str| > 0 && is_digit_string(num_str) { // Ensure num_str is not empty and contains only digits
            sum := sum + parse_int(num_str);
        }
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
    var lines_to_skip := test_idx * 2 + 1;
    for i := 0 to lines_to_skip
        invariant 0 <= i <= lines_to_skip
        invariant current_line_start >= T_line_end_idx + 1
        invariant (i == 0 && current_line_start == T_line_end_idx + 1) || (i > 0 && stdin_input[current_line_start-1] == '\n')
        decreases lines_to_skip - i
    {
        var next_newline_idx := stdin_input.IndexOf('\n', current_line_start);
        if next_newline_idx == -1 then return 0; // Should not happen given full input validity
        current_line_start := next_newline_idx + 1;
    }

    // current_line_start is now the start of the target M line for test_idx
    var m_line_end_idx := stdin_input.IndexOf('\n', current_line_start);
    if m_line_end_idx == -1 then return 0; // Should not happen
    var m_str := stdin_input[current_line_start .. m_line_end_idx];
    
    // Ensure m_str contains only digits before parsing
    if |m_str| > 0 && is_digit_string(m_str) then
        parse_int(m_str)
    else
        0 // Should not happen given valid_input_format
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

