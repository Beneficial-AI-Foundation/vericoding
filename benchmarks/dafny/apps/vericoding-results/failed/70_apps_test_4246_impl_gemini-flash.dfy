// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed `parse_lines` to correctly parse lines and handle the last line not ending with a newline. */
function parse_lines(input: string): seq<string>
    reads input
{
    var lines: seq<string> := [];
    var start := 0;
    while start < |input|
        invariant 0 <= start <= |input|
    {
        var end := start;
        while end < |input| && input[end] != '\n'
            invariant start <= end <= |input|
            invariant forall i :: start <= i < end ==> input[i] != '\n'
        {
            end := end + 1;
        }
        lines := lines + [input[start..end]];
        if end < |input| && input[end] == '\n' {
            start := end + 1;
        } else {
            start := end;
        }
    }
    return lines;
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
/* code modified by LLM (iteration 5): Calls compute_result to satisfy the postcondition. */
{
  result := compute_result(input);
}
// </vc-code>
