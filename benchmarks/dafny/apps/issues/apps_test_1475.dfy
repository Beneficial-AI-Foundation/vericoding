// <vc-preamble>
function split_lines(s: string): seq<string>
{
    ["", ""]
}

function can_parse_first_line(line: string): bool
{
    true
}

function can_parse_second_line(line: string): bool
{
    true
}

function valid_input_constraints(line1: string, line2: string): bool
    requires can_parse_first_line(line1) && can_parse_second_line(line2)
{
    var (n, b, k, x) := parse_first_line(line1);
    var block := parse_second_line(line2);
    2 <= n <= 50000 &&
    1 <= b <= 1000000000 &&
    0 <= k < x &&
    2 <= x <= 100 &&
    |block| == n &&
    forall i :: 0 <= i < |block| ==> 1 <= block[i] <= 9
}

function parse_first_line(line: string): (int, int, int, int)
    requires can_parse_first_line(line)
{
    (2, 1, 0, 2)
}

function parse_second_line(line: string): seq<int>
    requires can_parse_second_line(line)
{
    [1, 1]
}

function int_to_string(n: nat): string
    ensures |int_to_string(n)| > 0
    ensures forall i :: 0 <= i < |int_to_string(n)| ==> '0' <= int_to_string(n)[i] <= '9'
{
    "0"
}

function count_ways(n: int, b: int, k: int, x: int, block: seq<int>): nat
    requires 2 <= n <= 50000
    requires 1 <= b <= 1000000000
    requires 0 <= k < x
    requires 2 <= x <= 100
    requires |block| == n
    requires forall i :: 0 <= i < |block| ==> 1 <= block[i] <= 9
    ensures count_ways(n, b, k, x, block) >= 0
{
    0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires exists lines :: 
        lines == split_lines(stdin_input) && 
        |lines| >= 2 &&
        can_parse_first_line(lines[0]) &&
        can_parse_second_line(lines[1]) &&
        valid_input_constraints(lines[0], lines[1])
    ensures |result| > 0
    ensures exists num: nat :: 
        result == int_to_string(num) + "\n" &&
        0 <= num < 1000000007
    ensures forall i :: 0 <= i < |result| - 1 ==> '0' <= result[i] <= '9'
    ensures result[|result|-1] == '\n'
    ensures exists lines, n, b, k, x, block ::
        lines == split_lines(stdin_input) &&
        parse_first_line(lines[0]) == (n, b, k, x) &&
        parse_second_line(lines[1]) == block &&
        result == int_to_string(count_ways(n, b, k, x, block) % 1000000007) + "\n"
// </vc-spec>
// <vc-code>
{
    var lines := split_lines(stdin_input);
    var (n, b, k, x) := parse_first_line(lines[0]);
    var block := parse_second_line(lines[1]);
    var ways := count_ways(n, b, k, x, block);
    var answer := ways % 1000000007;
    result := int_to_string(answer) + "\n";
}
// </vc-code>
