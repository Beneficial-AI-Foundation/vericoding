predicate ValidInput(stdin_input: string)
{
    var lines := split_lines(stdin_input);
    |lines| >= 3 && 
    var n := parse_int(lines[0]);
    var x_line := parse_int_list(lines[1]);
    var y_line := parse_int_list(lines[2]);
    n >= 1 && |x_line| > 0 && |y_line| > 0 &&
    x_line[0] >= 0 && y_line[0] >= 0 &&
    |x_line| >= 1 + x_line[0] && |y_line| >= 1 + y_line[0]
}

function GetExpectedOutput(stdin_input: string): string
    requires ValidInput(stdin_input)
{
    var lines := split_lines(stdin_input);
    var n := parse_int(lines[0]);
    var x_line := parse_int_list(lines[1]);
    var y_line := parse_int_list(lines[2]);
    var x_levels := set_from_seq(x_line[1..1+x_line[0]]);
    var y_levels := set_from_seq(y_line[1..1+y_line[0]]);
    var all_levels := x_levels + y_levels;
    var required_levels := set i {:trigger} | 1 <= i <= n :: i;
    if all_levels >= required_levels then "I become the guy." else "Oh, my keyboard!"
}

function set_from_seq(s: seq<int>): set<int>
{
    set x | x in s
}

function split_lines(s: string): seq<string>
    decreases |s|
{
    if |s| == 0 then []
    else
        var newline_pos := find_char(s, '\n');
        if newline_pos == -1 then [trim(s)]
        else if 0 <= newline_pos < |s| then 
            [trim(s[0..newline_pos])] + split_lines(s[newline_pos+1..])
        else [trim(s)]
}

function trim(s: string): string
{
    if |s| == 0 then s
    else if s[|s|-1] == '\r' then s[0..|s|-1]
    else s
}

function find_char(s: string, c: char): int
    ensures find_char(s, c) == -1 || (0 <= find_char(s, c) < |s|)
    decreases |s|
{
    if |s| == 0 then -1
    else if s[0] == c then 0
    else
        var rest := find_char(s[1..], c);
        if rest == -1 then -1 else rest + 1
}

function parse_int(s: string): int
{
    if |s| == 0 then 0
    else if s[0] == '-' then 
        if is_valid_digits(s[1..]) then -parse_int_helper(s[1..]) else 0
    else if is_valid_digits(s) then parse_int_helper(s) else 0
}

predicate is_valid_digits(s: string) {
    forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function parse_int_helper(s: string): int
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    decreases |s|
{
    if |s| == 0 then 0
    else if |s| == 1 then char_to_digit(s[0])
    else parse_int_helper(s[0..|s|-1]) * 10 + char_to_digit(s[|s|-1])
}

function char_to_digit(c: char): int
    requires '0' <= c <= '9'
{
    (c as int) - ('0' as int)
}

function parse_int_list(s: string): seq<int>
{
    var parts := split_by_char(s, ' ');
    seq(|parts|, i requires 0 <= i < |parts| => parse_int(parts[i]))
}

function split_by_char(s: string, delimiter: char): seq<string>
    decreases |s|
{
    if |s| == 0 then []
    else
        var delim_pos := find_char(s, delimiter);
        if delim_pos == -1 then [s]
        else if delim_pos == 0 then split_by_char(s[1..], delimiter)
        else if 0 < delim_pos < |s| then 
            [s[0..delim_pos]] + split_by_char(s[delim_pos+1..], delimiter)
        else [s]
}

// <vc-helpers>
lemma SetFromSeqSubset(s: seq<int>, start: int, end: int)
    requires 0 <= start <= end <= |s|
    ensures set_from_seq(s[start..end]) <= set_from_seq(s)
{
    var sub := s[start..end];
    forall x | x in set_from_seq(sub)
    ensures x in set_from_seq(s)
    {
        assert x in sub;
        assert exists i :: 0 <= i < |sub| && sub[i] == x;
        var i :| 0 <= i < |sub| && sub[i] == x;
        assert s[start + i] == x;
        assert x in s;
    }
}

lemma SetUnionCommutative(a: set<int>, b: set<int>)
    ensures a + b == b + a
{
}

lemma SetComparisonTransitive(a: set<int>, b: set<int>, c: set<int>)
    requires a >= b && b >= c
    ensures a >= c
{
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures result == GetExpectedOutput(stdin_input)
// </vc-spec>
// <vc-code>
{
    var lines := split_lines(stdin_input);
    var n := parse_int(lines[0]);
    var x_line := parse_int_list(lines[1]);
    var y_line := parse_int_list(lines[2]);
    
    var x_levels := set_from_seq(x_line[1..1+x_line[0]]);
    var y_levels := set_from_seq(y_line[1..1+y_line[0]]);
    var all_levels := x_levels + y_levels;
    var required_levels := set i {:trigger} | 1 <= i <= n :: i;
    
    if all_levels >= required_levels {
        result := "I become the guy.";
    } else {
        result := "Oh, my keyboard!";
    }
}
// </vc-code>

