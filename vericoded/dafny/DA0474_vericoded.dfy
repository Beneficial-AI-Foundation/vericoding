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
    var n := string_to_nat(lines[0]);
    var s := lines[1];
    result := caesar_shift(s, n) + "\n";
}
// </vc-code>

