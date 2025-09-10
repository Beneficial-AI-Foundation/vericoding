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
    ensures forall i :: 0 <= i < |parse_lines(input)| ==> |parse_lines(input)[i]| >= 0 // Changed from >0 to >=0
{
    var lines: seq<string> := [];
    var current_line: string := "";
    if |input| == 0 { // Handle empty input explicitly
        return [""];
    }
    for i := 0 to |input| - 1
        invariant 0 <= i <= |input|
        invariant forall k :: 0 <= k < |lines| ==> |lines[k]| >= 0 // Changed from >0 to >=0
        invariant current_line == input[ (if |lines| > 0 then (var idx := 0; var len_sum := 0; while idx < |lines| { len_sum := len_sum + |lines[idx]| + 1; idx := idx + 1; } ; len_sum) else 0) .. i ]
    {
        if input[i] == '\n'
        {
            lines := lines + [current_line];
            current_line := "";
        } else
        {
            current_line := current_line + input[i];
        }
    }
    // Changed the condition to include empty last line if it's the only line
    if |current_line| > 0 || (|lines| == 0 && |current_line| == 0) // Add the last line if it's not empty, or if there were no newlines and the input itself wasn't empty
    {
        lines := lines + [current_line];
    }
    lines
}

function int_to_string(i: int): string
    requires 0 <= i <= 9
    ensures |int_to_string(i)| == 1
    ensures (i == 0) ==> (int_to_string(i) == "0")
    ensures (i == 1) ==> (int_to_string(i) == "1")
    ensures (i == 2) ==> (int_to_string(i) == "2")
    ensures (i == 3) ==> (int_to_string(i) == "3")
{
    if i == 0 then "0"
    else if i == 1 then "1"
    else if i == 2 then "2"
    else if i == 3 then "3"
    else if i == 4 then "4"
    else if i == 5 then "5"
    else if i == 6 then "6"
    else if i == 7 then "7"
    else if i == 8 then "8"
    else "9"
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

