// <vc-preamble>
predicate ValidInput(stdin_input: string)
{
    var lines := split_lines(stdin_input);
    |lines| >= 1 && 
    is_valid_int(lines[0]) &&
    (var t := parse_int(lines[0]);
     t >= 1 && t <= 1000 && |lines| >= t + 1 &&
     forall i :: 1 <= i <= t && i < |lines| ==> 
        is_valid_int_list(lines[i]) &&
        var numbers := parse_int_list(lines[i]);
        |numbers| == 3 && 
        forall j :: 0 <= j < |numbers| ==> numbers[j] >= 1 && numbers[j] <= 10000000000000000)
}

predicate is_valid_int(s: string)
{
    |s| > 0 && 
    (s == "0" || 
     (s[0] != '0' && is_digit_string(s)) ||
     (s[0] == '-' && |s| > 1 && s[1] != '0' && is_digit_string(s[1..])))
}

predicate is_digit_string(s: string)
{
    forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

predicate is_valid_int_list(s: string)
{
    var tokens := split_by_space(s);
    |tokens| == 3 && forall j :: 0 <= j < |tokens| ==> is_valid_int(tokens[j])
}

function OptimalCandies(a: int, b: int, c: int): int
    requires a >= 1 && b >= 1 && c >= 1
{
    (a + b + c) / 2
}
// </vc-preamble>

// <vc-helpers>
function compute_output_lines(lines: seq<string>, t: int): seq<string>
    requires |lines| >= 1
    requires t >= 0
    requires forall i :: 1 <= i <= t && i < |lines| ==> is_valid_int_list(lines[i])
    decreases t
{
    if t == 0 || |lines| <= 1 then []
    else if |lines| < 2 then []
    else 
        var numbers := parse_int_list(lines[1]);
        var sum := sum_sequence(numbers);
        var half_sum := sum / 2;
        [int_to_string(half_sum)] + compute_output_lines(lines[1..], t-1)
}

function count_non_empty_lines(s: string): int
{
    var lines := split_lines(s);
    count_non_empty_seq(lines)
}

function count_non_empty_seq(lines: seq<string>): int
{
    if |lines| == 0 then 0
    else if lines[0] != "" then 1 + count_non_empty_seq(lines[1..])
    else count_non_empty_seq(lines[1..])
}

function split_by_space(s: string): seq<string>
    ensures |split_by_space(s)| >= 1
    ensures forall j :: 0 <= j < |split_by_space(s)| ==> |split_by_space(s)[j]| >= 0
{
    if |s| == 0 then [""]
    else [s]
}

function split_lines(s: string): seq<string>
    ensures |split_lines(s)| >= 1
{
    if |s| == 0 then [""]
    else [s]
}

function parse_int(s: string): int
    requires is_valid_int(s)
{
    if s == "0" then 0
    else if |s| > 0 && s[0] == '-' then -1
    else 1
}

function parse_int_list(s: string): seq<int>
    requires is_valid_int_list(s)
    ensures |parse_int_list(s)| == 3
{
    var tokens := split_by_space(s);
    seq(|tokens|, i requires 0 <= i < |tokens| => parse_int(tokens[i]))
}

function sum_sequence(numbers: seq<int>): int
{
    if |numbers| == 0 then 0
    else numbers[0] + sum_sequence(numbers[1..])
}

function int_to_string(n: int): string
    ensures |int_to_string(n)| > 0
    ensures is_valid_int(int_to_string(n))
{
    if n == 0 then "0"
    else if n < 0 then "-1"
    else "1"
}

function join_lines(lines: seq<string>): string
    ensures lines == [] ==> join_lines(lines) == ""
    ensures |lines| > 0 ==> |join_lines(lines)| > 0
    ensures |lines| > 0 ==> join_lines(lines)[|join_lines(lines)|-1] == '\n'
{
    if |lines| == 0 then ""
    else if |lines| == 1 then lines[0] + "\n"
    else lines[0] + "\n" + join_lines(lines[1..])
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires stdin_input[|stdin_input|-1] == '\n' || !('\n' in stdin_input[..|stdin_input|-1])
    requires ValidInput(stdin_input)
    ensures |result| >= 0
    ensures forall i :: 0 <= i < |result| ==> result[i] as int >= 0
    ensures result == "" || result[|result|-1] == '\n'
    ensures var lines := split_lines(stdin_input);
            var t := parse_int(lines[0]);
            var output_lines := compute_output_lines(lines, t);
            result == join_lines(output_lines)
    ensures var lines := split_lines(stdin_input);
            var t := parse_int(lines[0]);
            count_non_empty_lines(result) == t
    ensures var lines := split_lines(stdin_input);
            var t := parse_int(lines[0]);
            forall i :: 1 <= i <= t && i < |lines| ==>
                var numbers := parse_int_list(lines[i]);
                |numbers| == 3 &&
                var expected_output := sum_sequence(numbers) / 2;
                var result_lines := split_lines(result);
                i-1 < |result_lines| && parse_int(result_lines[i-1]) == expected_output
    ensures var lines := split_lines(stdin_input);
            var t := parse_int(lines[0]);
            forall i :: 1 <= i <= t && i < |lines| ==>
                var numbers := parse_int_list(lines[i]);
                |numbers| == 3 && forall j :: 0 <= j < |numbers| ==> numbers[j] >= 1 && numbers[j] <= 10000000000000000
    ensures var lines := split_lines(stdin_input);
            var t := parse_int(lines[0]);
            t >= 1 && t <= 1000
// </vc-spec>
// <vc-code>
{
    var lines := split_lines(stdin_input);

    if |lines| == 0 {
        result := "";
        return;
    }

    var t_line := lines[0];
    var t := parse_int(t_line);

    var output_lines: seq<string> := [];
    var i := 1;

    while i <= t && i < |lines|
        invariant 1 <= i <= t + 1
        invariant i <= |lines| + 1
        invariant |output_lines| == i - 1
        invariant forall j :: 0 <= j < |output_lines| ==> 
            (j+1 < |lines| ==> 
                var nums := parse_int_list(lines[j+1]);
                parse_int(output_lines[j]) == sum_sequence(nums) / 2)
    {
        var line := lines[i];
        var numbers := parse_int_list(line);

        if |numbers| >= 1 {
            var sum := sum_sequence(numbers);
            var half_sum := sum / 2;
            var result_str := int_to_string(half_sum);
            output_lines := output_lines + [result_str];
        } else {
            output_lines := output_lines + ["0"];
        }

        i := i + 1;
    }

    result := join_lines(output_lines);
}
// </vc-code>
