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

// <vc-helpers>
function int_to_string(i: int): string
    requires 0 <= i <= 3
    ensures |int_to_string(i)| == 1 && int_to_string(i)[0] in {'0', '1', '2', '3'}
{
    if i == 0 then "0"
    else if i == 1 then "1"
    else if i == 2 then "2"
    else "3"
}

function parse_lines(input: string): seq<string>
    decreases |input|
{
    if input == "" then []
    else if input[0] == '\n' then [] + parse_lines(input[1..])
    else
        var line, rest := extract_first_line(input);
        [line] + parse_lines(rest)
}

function extract_first_line(s: string): (string, string)
    requires |s| > 0 && s[0] != '\n'
    ensures var line, rest := extract_first_line(s); s == line + rest
    decreases |s|
{
    if |s| == 1 then (s, "")
    else if s[1] == '\n' then (s[0..1], s[1..])
    else
        var line', rest' := extract_first_line(s[1..]);
        (s[0..1] + line', rest')
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    ensures result == compute_result(input)
    ensures |result| >= 2 && result[|result|-1] == '\n'
    ensures result[0] in
// </vc-spec>
// <vc-code>
{
    result := compute_result(input);
}
// </vc-code>

