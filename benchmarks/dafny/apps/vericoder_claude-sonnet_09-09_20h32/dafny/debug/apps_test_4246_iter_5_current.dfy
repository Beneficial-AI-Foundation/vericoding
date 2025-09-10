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
function parse_lines(input: string): seq<string>
{
    if |input| == 0 then []
    else 
        var newline_pos := find_newline(input, 0);
        if newline_pos == -1 then [input]
        else [input[0..newline_pos]] + parse_lines(input[newline_pos+1..])
}

function find_newline(s: string, start: int): int
    requires 0 <= start <= |s|
    ensures find_newline(s, start) == -1 || (start <= find_newline(s, start) < |s| && s[find_newline(s, start)] == '\n')
{
    if start >= |s| then -1
    else if s[start] == '\n' then start
    else find_newline(s, start + 1)
}

function int_to_string(n: int): string
    requires 0 <= n <= 3
    ensures |int_to_string(n)| == 1
    ensures int_to_string(n)[0] in {'0', '1', '2', '3'}
{
    if n == 0 then "0"
    else if n == 1 then "1"
    else if n == 2 then "2"
    else "3"
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
    var lines := parse_lines(input);
    if |lines| < 2 then
        result := "0\n";
    else if |lines[0]| != 3 || |lines[1]| != 3 then
        result := "0\n";
    else
        var matches := count_matches(lines[0], lines[1]);
        result := int_to_string(matches) + "\n";
}
// </vc-code>

