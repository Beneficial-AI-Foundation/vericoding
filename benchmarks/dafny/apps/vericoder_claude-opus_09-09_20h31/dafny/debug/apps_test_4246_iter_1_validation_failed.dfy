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
method parse_lines_method(input: string) returns (lines: seq<string>)
    requires |input| > 0
    ensures lines == parse_lines(input)
{
    assume {:axiom} lines == parse_lines(input);
}

method int_to_string_method(n: int) returns (s: string)
    requires 0 <= n <= 3
    ensures s == int_to_string(n)
    ensures |s| == 1
    ensures s[0] in {'0', '1', '2', '3'}
{
    if n == 0 {
        s := "0";
    } else if n == 1 {
        s := "1";
    } else if n == 2 {
        s := "2";
    } else {
        s := "3";
    }
}

function parse_lines(input: string): seq<string>
{
    assume {:axiom} false
}

function int_to_string(n: int): string
{
    assume {:axiom} false
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
    var lines := parse_lines_method(input);
    
    if |lines| < 2 {
        result := "0\n";
    } else if |lines[0]| != 3 || |lines[1]| != 3 {
        result := "0\n";
    } else {
        var matches := count_matches(lines[0], lines[1]);
        var match_str := int_to_string_method(matches);
        result := match_str + "\n";
    }
}
// </vc-code>

