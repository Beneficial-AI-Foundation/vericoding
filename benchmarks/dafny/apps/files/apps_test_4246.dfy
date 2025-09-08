Given two strings S and T, each of length 3, representing weather forecasts and actual weather 
respectively for 3 consecutive days, count how many days the forecast was correct.
Each character represents weather: 'S' = sunny, 'C' = cloudy, 'R' = rainy.
Input: Two lines with strings of length 3 containing only 'S', 'C', 'R' characters.
Output: Integer representing the number of days where forecast matched actual weather.

predicate is_valid_input(input: string)
    requires |input| > 0
{
    var lines := parse_lines(input);
    |lines| >= 2 && |lines[0]| == 3 && |lines[1]| == 3
}

function count_matches_from_input(input: string): int
    requires |input| > 0
    requires is_valid_input(input)
    ensures 0 <= count_matches_from_input(input) <= 3
{
    var lines := parse_lines(input);
    count_matches(lines[0], lines[1])
}

function count_matches(s: string, t: string): int
    requires |s| == |t| == 3
    ensures 0 <= count_matches(s, t) <= 3
    ensures count_matches(s, t) == 
        (if s[0] == t[0] then 1 else 0) +
        (if s[1] == t[1] then 1 else 0) +
        (if s[2] == t[2] then 1 else 0)
{
    (if s[0] == t[0] then 1 else 0) +
    (if s[1] == t[1] then 1 else 0) +
    (if s[2] == t[2] then 1 else 0)
}

function compute_result(input: string): string
    requires |input| > 0
    ensures |compute_result(input)| >= 2
    ensures compute_result(input)[|compute_result(input)|-1] == '\n'
    ensures compute_result(input)[0] in {'0', '1', '2', '3'}
    ensures is_valid_input(input) ==> 
        compute_result(input) == int_to_string(count_matches_from_input(input)) + "\n"
    ensures !is_valid_input(input) ==> compute_result(input) == "0\n"
{
    var lines := parse_lines(input);
    if |lines| < 2 then "0\n"
    else if |lines[0]| != 3 || |lines[1]| != 3 then "0\n"
    else int_to_string(count_matches(lines[0], lines[1])) + "\n"
}

function int_to_string(n: int): string
    requires 0 <= n <= 3
    ensures int_to_string(n) in ["0", "1", "2", "3"]
    ensures |int_to_string(n)| == 1
    ensures n == 0 ==> int_to_string(n) == "0"
    ensures n == 1 ==> int_to_string(n) == "1"
    ensures n == 2 ==> int_to_string(n) == "2"
    ensures n == 3 ==> int_to_string(n) == "3"
{
    if n == 0 then "0"
    else if n == 1 then "1"
    else if n == 2 then "2"
    else "3"
}

function parse_lines(input: string): seq<string>
    requires |input| > 0
    ensures |parse_lines(input)| >= 0
    ensures forall i :: 0 <= i < |parse_lines(input)| ==> |parse_lines(input)[i]| >= 0
{
    parse_lines_helper(input, 0, "", [])
}

function parse_lines_helper(input: string, pos: int, current: string, lines: seq<string>): seq<string>
    requires 0 <= pos <= |input|
    requires |input| > 0
    ensures |parse_lines_helper(input, pos, current, lines)| >= 0
    decreases |input| - pos
{
    if pos >= |input| then
        if current == "" then lines else lines + [current]
    else if input[pos] == '\n' then
        if current == "" then 
            parse_lines_helper(input, pos + 1, "", lines)
        else 
            parse_lines_helper(input, pos + 1, "", lines + [current])
    else if input[pos] == '\r' then
        parse_lines_helper(input, pos + 1, current, lines)
    else
        parse_lines_helper(input, pos + 1, current + [input[pos]], lines)
}

method split_lines(input: string) returns (lines: seq<string>)
    requires |input| > 0
    ensures lines == parse_lines(input)
{
    lines := parse_lines_helper(input, 0, "", []);
}

method solve(input: string) returns (result: string)
    requires |input| > 0
    ensures result == compute_result(input)
    ensures |result| >= 2 && result[|result|-1] == '\n'
    ensures result[0] in
{'0', '1', '2', '3'}
