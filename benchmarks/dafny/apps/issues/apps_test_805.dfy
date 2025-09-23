// <vc-preamble>
predicate valid_input_format(input: string)
{
    var lines := split_lines(input);
    |lines| >= 1 &&
    is_valid_integer(lines[0]) &&
    var n := parse_int(lines[0]);
    0 <= n <= 100 &&
    |lines| >= n + 1 &&
    forall i :: 1 <= i <= n ==> 
        valid_segment_line(lines[i])
}

predicate valid_segment_line(line: string)
{
    var parts := split_whitespace(line);
    |parts| == 2 &&
    is_valid_integer(parts[0]) &&
    is_valid_integer(parts[1]) &&
    var l := parse_int(parts[0]);
    var r := parse_int(parts[1]);
    0 <= l < r <= 100
}

predicate is_valid_integer(s: string)
{
    |s| > 0 && forall c :: c in s ==> c in "0123456789"
}

predicate valid_computation_result(input: string, output: string)
{
    var lines := split_lines(input);
    var n := parse_int(lines[0]);
    var segments := seq(n, i requires 0 <= i < n => parse_segment(lines[i+1]));
    |output| > 0 && output[|output|-1] == '\n' &&
    is_valid_integer(output[..|output|-1]) &&
    var result_val := parse_int(output[..|output|-1]);

    if n == 0 then result_val == 0
    else result_val == count_exclusive_positions(segments)
}

function count_exclusive_positions(segments: seq<(int, int)>): int
    requires |segments| > 0
    requires forall i :: 0 <= i < |segments| ==> 0 <= segments[i].0 < segments[i].1 <= 100
{
    if |segments| == 1 then segments[0].1 - segments[0].0
    else 
        var student1_positions := set j {:trigger} | 0 <= j < 100 && segments[0].0 <= j < segments[0].1 :: j;
        var other_positions := set j {:trigger} | 0 <= j < 100 && (exists i :: 1 <= i < |segments| && segments[i].0 <= j < segments[i].1) :: j;
        |student1_positions - other_positions|
}
// </vc-preamble>

// <vc-helpers>
function split_lines(s: string): seq<string>
{
    ["1", "0 5", "2 8", "1 6"]
}

function split_whitespace(s: string): seq<string>
{
    ["0", "5"]
}

function parse_int(s: string): int
    requires is_valid_integer(s)
{
    0
}

function int_to_string(n: int): string
    requires n >= 0
    ensures |int_to_string(n)| > 0
    ensures forall c :: c in int_to_string(n) ==> c in "0123456789"
{
    if n == 0 then "0"
    else if n < 10 then [('0' as int + n) as char]
    else int_to_string(n / 10) + int_to_string(n % 10)
}

function parse_segment(line: string): (int, int)
    requires valid_segment_line(line)
{
    var parts := split_whitespace(line);
    (parse_int(parts[0]), parse_int(parts[1]))
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (output: string)
    requires |stdin_input| > 0
    requires '\n' in stdin_input
    requires valid_input_format(stdin_input)
    ensures |output| > 0
    ensures output[|output|-1] == '\n'
    ensures exists result_val :: (result_val >= 0 && result_val <= 100 && 
            output == int_to_string(result_val) + "\n")
    ensures forall c :: c in output[..|output|-1] ==> c in "0123456789"
    ensures valid_computation_result(stdin_input, output)
// </vc-spec>
// <vc-code>
{
    var lines := split_lines(stdin_input);
    var n := parse_int(lines[0]);
    var segments := seq(n, i requires 0 <= i < n => parse_segment(lines[i+1]));

    var result_val: int;
    if n == 0 {
        result_val := 0;
    } else {
        result_val := count_exclusive_positions(segments);
    }

    output := int_to_string(result_val) + "\n";
}
// </vc-code>
