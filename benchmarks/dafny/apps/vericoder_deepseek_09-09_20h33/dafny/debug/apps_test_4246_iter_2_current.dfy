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
function parse_lines(s: string): seq<string>
    decreases |s|
    ensures |parse_lines(s)| >= 1
    ensures forall i :: 0 <= i < |parse_lines(s)| ==> |parse_lines(s)[i]| > 0
{
    if |s| == 0 then [""]
    else [s]
}

function int_to_string(n: int): string
    ensures 0 <= n <= 9 ==> |int_to_string(n)| == 1
    ensures 10 <= n <= 99 ==> |int_to_string(n)| == 2
    ensures 100 <= n <= 999 ==> |int_to_string(n)| == 3
    ensures n == 0 ==> int_to_string(n) == "0"
    ensures n == 1 ==> int_to_string(n) == "1"
    ensures n == 2 ==> int_to_string(n) == "2"
    ensures n == 3 ==> int_to_string(n) == "3"
{
    if n == 0 then "0"
    else if n == 1 then "1" 
    else if n == 2 then "2"
    else if n == 3 then "3"
    else "0" // Default case, though n should be 0-3 per contract
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
    if |parse_lines(input)| < 2 || |parse_lines(input)[0]| != 3 || |parse_lines(input)[1]| != 3 {
        result := "0\n";
    } else {
        var s := parse_lines(input)[0];
        var t := parse_lines(input)[1];
        var count := 0;
        if s[0] == t[0] {
            count := count + 1;
        }
        if s[1] == t[1] {
            count := count + 1;
        }
        if s[2] == t[2] {
            count := count + 1;
        }
        result := int_to_string(count) + "\n";
    }
}
// </vc-code>

