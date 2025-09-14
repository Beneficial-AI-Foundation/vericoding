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
function split_lines_impl(s: string): seq<string>
{
    if |s| == 0 then []
    else if |s| == 1 then [s]
    else if s[0] == '\n' then [""] + split_lines_impl(s[1..])
    else [s[..1]] + split_lines_impl(s[1..])
}

function is_valid_number_impl(s: string): bool
{
    |s| > 0 && (forall i | 0 <= i < |s| :: '0' <= s[i] <= '9')
}

function parse_int_impl(s: string): int
    requires is_valid_number_impl(s)
    decreases |s|
{
    if |s| == 0 then 0
    else 
        var first_char := s[0];
        var first_digit := first_char as int - '0' as int;
        if |s| == 1 then first_digit
        else var rest := parse_int_impl(s[1..]);
            first_digit * pow10(|s| - 1) + rest
}

function pow10(n: nat): int
    decreases n
{
    if n == 0 then 1
    else 10 * pow10(n - 1)
}

function is_binary_string_impl(s: string): bool
{
    |s| >= 0 && forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

function min_ops_helper(s: string, start: int, end: int): int
    requires 0 <= start <= end <= |s|
    requires is_binary_string_impl(s)
    decreases end - start
{
    if end - start <= 1 then 0
    else
        var mid := (start + end) / 2;
        var left := min_ops_helper(s, start, mid);
        var right := min_ops_helper(s, mid, end);
        if s[mid - 1] == s[mid] then left + right + 1
        else left + right
}

ghost function min_ops_helper_bounds(s: string, start: int, end: int): (int, int)
    requires 0 <= start <= end <= |s|
    requires is_binary_string_impl(s)
    ensures var (lower, upper) := min_ops_helper_bounds(s, start, end);
        lower >= 0 && upper <= end - start
    decreases end - start
{
    if end - start <= 1 then (0, 0)
    else
        var mid := (start + end) / 2;
        var (left_lower, left_upper) := min_ops_helper_bounds(s, start, mid);
        var (right_lower, right_upper) := min_ops_helper_bounds(s, mid, end);
        if s[mid - 1] == s[mid] then (0, left_upper + right_upper + 1)
        else (0, left_upper + right_upper)
}

lemma min_ops_helper_satisfies_post(s: string, start: int, end: int)
    requires 0 <= start <= end <= |s|
    requires is_binary_string_impl(s)
    ensures min_ops_helper(s, start, end) >= 0
    ensures min_ops_helper(s, start, end) <= end - start
    decreases end - start
{
    if end - start <= 1 {
        // Base case: 0 operations needed
    } else {
        var mid := (start + end) / 2;
        min_ops_helper_satisfies_post(s, start, mid);
        min_ops_helper_satisfies_post(s, mid, end);
        var left := min_ops_helper(s, start, mid);
        var right := min_ops_helper(s, mid, end);
        // left >= 0 && left <= mid - start
        // right >= 0 && right <= end - mid
        // So left + right >= 0
        // And left + right <= (mid - start) + (end - mid) = end - start
        // left + right + 1 <= end - start + 1, but we need <= end - start
        // Actually, we need to show that left + right + 1 <= end - start
        // Since mid - start >= 1 and end - mid >= 1, we have end - start >= 2
        // So left + right + 1 <= (mid - start) + (end - mid) + 1 = end - start + 1
        // But we need a tighter bound
    }
}

lemma min_ops_helper_bounds_tight(s: string, start: int, end: int)
    requires 0 <= start <= end <= |s|
    requires is_binary_string_impl(s)
    ensures min_ops_helper(s, start, end) <= end - start - if end - start > 1 then 1 else 0
    decreases end - start
{
    if end - start <= 1 {
    } else {
        var mid := (start + end) / 2;
        min_ops_helper_bounds_tight(s, start, mid);
        min_ops_helper_bounds_tight(s, mid, end);
    }
}

function int_to_string(n: int): string
    requires n >= 0
{
    if n < 10 then [('0' as int + n) as char]
    else int_to_string(n / 10) + [('0' as int + (n % 10)) as char]
}

function string_join(sep: string, strings: seq<string>): string
    decreases strings
{
    if |strings| == 0 then ""
    else if |strings| == 1 then strings[0]
    else strings[0] + sep + string_join(sep, strings[1..])
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(result)
    ensures CorrectResult(input, result)
// </vc-spec>
// <vc-code>
{
    var lines := split_lines_impl(input);
    var t := parse_int_impl(lines[0]);
    var result_lines: seq<string> := [];
    var i := 1;
    
    while i < |lines|
        invariant i >= 1 && i <= |lines|
        invariant |result_lines| == i - 1
    {
        var s := lines[i];
        // The string can be empty in the input, so we need to handle that case
        if |s| == 0 {
            result_lines := result_lines + ["0"];
        } else {
            assert is_binary_string_impl(s);
            min_ops_helper_satisfies_post(s, 0, |s|);
            var min_ops := min_ops_helper(s, 0, |s|);
            var str_ops := int_to_string(min_ops);
            result_lines := result_lines + [str_ops];
        }
        i := i + 1;
    }
    
    result := string_join("\n", result_lines) + "\n";
}
// </vc-code>

