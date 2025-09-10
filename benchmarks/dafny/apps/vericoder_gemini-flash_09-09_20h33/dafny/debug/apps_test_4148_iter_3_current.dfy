function split_lines(input: string): seq<string>
requires |input| > 0
{
    var newline_pos := find_newline(input, 0);
    if newline_pos == -1 then [input]
    else if newline_pos >= 0 && newline_pos < |input| then
        if newline_pos + 1 >= |input| then [input[..newline_pos], ""]
        else [input[..newline_pos], input[newline_pos+1..]]
    else [input]
}

function find_newline(input: string, start: int): int
requires 0 <= start <= |input|
ensures find_newline(input, start) == -1 || (0 <= find_newline(input, start) < |input|)
decreases |input| - start
{
    if start >= |input| then -1
    else if input[start] == '\n' then start
    else find_newline(input, start + 1)
}

function is_valid_number(s: string): bool
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function string_to_nat(s: string): nat
requires is_valid_number(s)
decreases |s|
{
    if |s| == 0 then 0
    else if |s| == 1 then (s[0] as int - '0' as int) as nat
    else (s[0] as int - '0' as int) as nat * 10 + string_to_nat(s[1..])
}

function caesar_shift(s: string, n: nat): string
requires forall i :: 0 <= i < |s| ==> 'A' <= s[i] <= 'Z'
requires n <= 26
decreases |s|
ensures |caesar_shift(s, n)| == |s|
ensures forall i :: 0 <= i < |s| ==> 'A' <= caesar_shift(s, n)[i] <= 'Z'
ensures forall i :: 0 <= i < |s| ==> 
    var shifted_val := (s[i] as int - 'A' as int + n) % 26;
    caesar_shift(s, n)[i] == (('A' as int + shifted_val) as char)
{
    if |s| == 0 then ""
    else 
        var shifted_val := (s[0] as int - 'A' as int + n) % 26;
        var shifted_char := ('A' as int + shifted_val) as char;
        [shifted_char] + caesar_shift(s[1..], n)
}

predicate ValidInput(input: string)
{
    |input| > 0 &&
    (exists i :: 0 <= i < |input| && input[i] == '\n') &&
    var lines := split_lines(input);
    |lines| >= 2 &&
    is_valid_number(lines[0]) &&
    string_to_nat(lines[0]) <= 26 &&
    |lines[1]| >= 1 && |lines[1]| <= 10000 &&
    (forall j :: 0 <= j < |lines[1]| ==> 'A' <= lines[1][j] <= 'Z')
}

// <vc-helpers>
function find_newline_idx(s: string, start: int): int
decreases |s| - start
{
    if start >= |s| then -1
    else if s[start] == '\n' then start
    else find_newline_idx(s, start + 1)
}

function split_lines_helper(input: string): seq<string>
{
    var newline_pos := find_newline_idx(input, 0);
    if newline_pos == -1 then [input]
    else if newline_pos + 1 >= |input| then [input[..newline_pos], ""]
    else [input[..newline_pos], input[newline_pos+1..]] // This directly models the original split_lines
}

lemma SplitLinesCorrect(input: string)
requires |input| > 0
ensures split_lines(input) == split_lines_helper(input)
{
    var newline_pos := find_newline(input, 0);
    if newline_pos == -1 {
        // [input] == [input]
    } else if newline_pos >= 0 && newline_pos < |input| {
        if newline_pos + 1 >= |input| {
            // [input[..newline_pos], ""] == [input[..newline_pos], ""]
        } else {
            // [input[..newline_pos], input[newline_pos+1..]] == [input[..newline_pos], input[newline_pos+1..]]
        }
    } else { // This case is actually impossible due to the 'ensures' clause of find_newline
        // find_newline returns -1 or a valid index.
        // If newline_pos == -1, it's handled above.
        // If find_newline returns a value >= |input| that is not -1, it would violate the postcondition
        // `0 <= find_newline(input, start) < |input|`. So, this branch is unreachable.
    }
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
requires ValidInput(input)
ensures var lines := split_lines(input);
        var n := string_to_nat(lines[0]);
        var s := lines[1];
        result == caesar_shift(s, n) + "\n"
// </vc-spec>
// <vc-code>
{
    var lines := split_lines(input);
    // The ValidInput predicate ensures that:
    // 1. |input| > 0
    // 2. (exists i :: 0 <= i < |input| && input[i] == '\n')
    // Thus, split_lines(input) will always produce a sequence with at least two elements,
    // where lines[0] is the part before the first newline and lines[1] is the part after.
    // Specifically, if input = "N\nS", lines = ["N", "S"].
    // If input = "N\n", lines = ["N", ""].

    // Property from ValidInput: |lines| >= 2
    // This allows safe indexing `lines[0]` and `lines[1]`.
    var n_str := lines[0];
    var s_str := lines[1];

    // Property from ValidInput: is_valid_number(lines[0])
    // This implies is_valid_number(n_str).
    var n := string_to_nat(n_str);
    // Property from ValidInput: string_to_nat(lines[0]) <= 26
    // This implies n <= 26.

    // Property from ValidInput: (forall j :: 0 <= j < |lines[1]| ==> 'A' <= lines[1][j] <= 'Z')
    // This implies (forall j :: 0 <= j < |s_str| ==> 'A' <= s_str[j] <= 'Z').
    // These match the preconditions for caesar_shift(s_str, n).
    var result_s := caesar_shift(s_str, n);
    result := result_s + "\n";
}
// </vc-code>

