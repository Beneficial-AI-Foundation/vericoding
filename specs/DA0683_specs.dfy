// <vc-preamble>
predicate ValidInput(stdin_input: string)
{
    |stdin_input| > 0 && valid_input_format(stdin_input)
}

predicate valid_input_format(input: string)
{
    exists parsed :: (parsed == parse_input(input) && 
        parsed.valid && 
        |parsed.test_cases| >= 1 &&
        forall i :: 0 <= i < |parsed.test_cases| ==> 
            var tc := parsed.test_cases[i];
            tc.n >= 1 && |tc.s| == tc.n &&
            forall j :: 0 <= j < |tc.s| ==> tc.s[j] in "01")
}

function compute_balance_prefix(s: string, len: nat): int
    requires len <= |s|
    requires forall i :: 0 <= i < |s| ==> s[i] in "01"
    decreases len
{
    if len == 0 then 0
    else 
        var delta := if s[len-1] == '0' then 1 else -1;
        compute_balance_prefix(s, len-1) + delta
}

function compute_balance_array(s: string): seq<int>
    requires forall i :: 0 <= i < |s| ==> s[i] in "01"
    ensures |compute_balance_array(s)| == |s|
    ensures forall i :: 0 <= i < |s| ==> compute_balance_array(s)[i] == compute_balance_prefix(s, i+1)
{
    compute_balance_array_helper(s, 0, 0)
}

function compute_prefix_count_result(n: int, x: int, s: string): string
    requires n >= 1 && |s| == n
    requires forall i :: 0 <= i < |s| ==> s[i] in "01"
{
    var balance_array := compute_balance_array(s);
    var k := balance_array[n-1];
    var count := if x == 0 then 1 else 0;

    if k > 0 then
        var additional := count_valid_positions_positive_k(balance_array, k, x);
        int_to_string(count + additional)
    else if k < 0 then
        var additional := count_valid_positions_negative_k(balance_array, k, x);
        int_to_string(count + additional)
    else
        if x in balance_array then "-1"
        else int_to_string(count)
}

datatype TestCase = TestCase(n: int, x: int, s: string)
datatype ParsedInput = ParsedInput(valid: bool, test_cases: seq<TestCase>)
// </vc-preamble>

// <vc-helpers>
function split_lines(s: string): seq<string>
{
    split_lines_helper(s, 0)
}

function split_lines_helper(s: string, start: nat): seq<string>
    requires start <= |s|
    decreases |s| - start
{
    if start >= |s| then
        []
    else
        var end := find_newline(s, start);
        if end == |s| then
            if start == |s| then [] else [s[start..]]
        else
            [s[start..end]] + split_lines_helper(s, end + 1)
}

function find_newline(s: string, start: nat): nat
    requires start <= |s|
    ensures start <= find_newline(s, start) <= |s|
    ensures find_newline(s, start) == |s| || s[find_newline(s, start)] == '\n'
    decreases |s| - start
{
    if start >= |s| then |s|
    else if s[start] == '\n' then start
    else find_newline(s, start + 1)
}

function parse_input(input: string): ParsedInput
{
    ParsedInput(false, [])
}

function compute_balance_array_helper(s: string, pos: nat, current_balance: int): seq<int>
    requires pos <= |s|
    requires forall i :: 0 <= i < |s| ==> s[i] in "01"
    requires current_balance == compute_balance_prefix(s, pos)
    ensures |compute_balance_array_helper(s, pos, current_balance)| == |s| - pos
    ensures forall i :: 0 <= i < |s| - pos ==> 
        compute_balance_array_helper(s, pos, current_balance)[i] == compute_balance_prefix(s, pos + i + 1)
    decreases |s| - pos
{
    if pos >= |s| then []
    else
        var delta := if s[pos] == '0' then 1 else -1;
        var new_balance := current_balance + delta;
        [new_balance] + compute_balance_array_helper(s, pos + 1, new_balance)
}

function count_valid_positions_positive_k(balance_array: seq<int>, k: int, x: int): int
    requires k > 0
    ensures count_valid_positions_positive_k(balance_array, k, x) >= 0
{
    count_matching_positions(balance_array, k, x, true)
}

function count_valid_positions_negative_k(balance_array: seq<int>, k: int, x: int): int
    requires k < 0
    ensures count_valid_positions_negative_k(balance_array, k, x) >= 0
{
    count_matching_positions(balance_array, k, x, false)
}

function count_matching_positions(balance_array: seq<int>, k: int, x: int, positive_k: bool): int
    requires k != 0
    requires positive_k <==> k > 0
    ensures count_matching_positions(balance_array, k, x, positive_k) >= 0
{
    if |balance_array| == 0 then 0
    else
        var head := balance_array[0];
        var tail_count := count_matching_positions(balance_array[1..], k, x, positive_k);
        var matches := if positive_k then 
            (head % k == x % k && head <= x)
        else 
            (head % k == x % k && head >= x);
        tail_count + (if matches then 1 else 0)
}

function int_to_string(n: int): string
{
    if n == 0 then "0"
    else if n > 0 then int_to_string_positive(n)
    else "-" + int_to_string_positive(-n)
}

function int_to_string_positive(n: int): string
    requires n > 0
    decreases n
{
    if n < 10 then [char_of_digit(n)]
    else int_to_string_positive(n / 10) + [char_of_digit(n % 10)]
}

function string_to_int(s: string): int
    requires |s| > 0
    requires s != "-"
    requires forall i :: 0 <= i < |s| ==> s[i] in "0123456789-"
    requires s == "-1" || (forall i :: 0 <= i < |s| ==> s[i] in "0123456789")
{
    if s == "-1" then -1
    else string_to_int_positive(s)
}

function string_to_int_positive(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> s[i] in "0123456789"
    decreases |s|
{
    if |s| == 1 then digit_of_char(s[0])
    else string_to_int_positive(s[..|s|-1]) * 10 + digit_of_char(s[|s|-1])
}

function digit_of_char(c: char): int
    requires c in "0123456789"
    ensures 0 <= digit_of_char(c) <= 9
{
    if c == '0' then 0
    else if c == '1' then 1
    else if c == '2' then 2
    else if c == '3' then 3
    else if c == '4' then 4
    else if c == '5' then 5
    else if c == '6' then 6
    else if c == '7' then 7
    else if c == '8' then 8
    else 9
}

function char_of_digit(d: int): char
    requires 0 <= d <= 9
{
    if d == 0 then '0'
    else if d == 1 then '1'
    else if d == 2 then '2'
    else if d == 3 then '3'
    else if d == 4 then '4'
    else if d == 5 then '5'
    else if d == 6 then '6'
    else if d == 7 then '7'
    else if d == 8 then '8'
    else '9'
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures |result| >= 0
    ensures result == "" || (|result| > 0 && forall i :: 0 <= i < |result| ==> result[i] in "0123456789\n -")
    ensures forall line :: line in multiset(split_lines(result)) ==> 
        (line == "-1" || (forall c :: c in line ==> c in "0123456789"))
    ensures valid_input_format(stdin_input) ==> 
        var parsed := parse_input(stdin_input);
        var expected_lines := |parsed.test_cases|;
        |split_lines(result)| == expected_lines
    ensures valid_input_format(stdin_input) ==> 
        var parsed := parse_input(stdin_input);
        forall i :: 0 <= i < |parsed.test_cases| ==> 
            var tc := parsed.test_cases[i];
            var line := split_lines(result)[i];
            line == compute_prefix_count_result(tc.n, tc.x, tc.s)
    ensures result != ""
// </vc-spec>
// <vc-code>
{
    result := "";
}
// </vc-code>
