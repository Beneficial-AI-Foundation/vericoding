predicate is_binary_string(s: string)
{
    forall i :: 0 <= i < |s| ==> s[i] == '0' || s[i] == '1'
}

predicate is_valid_integer(s: string)
{
    |s| > 0 && (s[0] != '0' || |s| == 1) && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function count_char(s: string, c: char): int
{
    if |s| == 0 then 0
    else (if s[0] == c then 1 else 0) + count_char(s[1..], c)
}

function abs_diff_count(s: string): int
    requires is_binary_string(s)
{
    var count0 := count_char(s, '0');
    var count1 := count_char(s, '1');
    if count1 >= count0 then count1 - count0 else count0 - count1
}

function int_to_string(n: int): string
    requires n >= 0
{
    if n == 0 then "0"
    else if n < 10 then [char_of_digit(n)]
    else int_to_string(n / 10) + [char_of_digit(n % 10)]
}

function char_of_digit(d: int): char
    requires 0 <= d <= 9
{
    match d
        case 0 => '0'
        case 1 => '1' 
        case 2 => '2'
        case 3 => '3'
        case 4 => '4'
        case 5 => '5'
        case 6 => '6'
        case 7 => '7'
        case 8 => '8'
        case 9 => '9'
}

function string_to_int(s: string): int
    requires is_valid_integer(s)
{
    if |s| == 0 then 0
    else if |s| == 1 then (s[0] as int) - ('0' as int)
    else string_to_int(s[0..|s|-1]) * 10 + ((s[|s|-1] as int) - ('0' as int))
}

// <vc-helpers>
lemma count_char_preserves_binary(s: string, c: char)
    requires is_binary_string(s)
    ensures count_char(s, c) >= 0
{
}

lemma abs_diff_count_non_negative(s: string)
    requires is_binary_string(s)
    ensures abs_diff_count(s) >= 0
{
    count_char_preserves_binary(s, '0');
    count_char_preserves_binary(s, '1');
}

lemma int_to_string_valid(n: int)
    requires n >= 0
    ensures is_valid_integer(int_to_string(n))
{
    if n == 0 {
    } else if n < 10 {
    } else {
        int_to_string_valid(n / 10);
    }
}

lemma find_newline_exists(s: string) returns (pos: int)
    requires |s| > 0
    requires exists i :: 0 <= i < |s| && s[i] == '\n'
    ensures 0 <= pos < |s|
    ensures s[pos] == '\n'
{
    for i := 0 to |s|
        invariant forall j :: 0 <= j < i ==> s[j] != '\n'
    {
        if s[i] == '\n' {
            return i;
        }
    }
    assert false;
}

lemma find_binary_end_exists(s: string, start: int) returns (end: int)
    requires 0 <= start < |s|
    ensures start <= end <= |s|
    ensures end == |s| || s[end] == '\n'
{
    for i := start to |s|
        invariant forall j :: start <= j < i ==> s[j] != '\n'
    {
        if s[i] == '\n' {
            return i;
        }
    }
    return |s|;
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires exists i :: 0 <= i < |stdin_input| && stdin_input[i] == '\n'
    requires exists newline_pos :: 0 <= newline_pos < |stdin_input| && stdin_input[newline_pos] == '\n' &&
             newline_pos + 1 < |stdin_input| &&
             exists binary_end :: newline_pos + 1 <= binary_end <= |stdin_input| &&
             (binary_end == |stdin_input| || stdin_input[binary_end] == '\n') &&
             is_valid_integer(stdin_input[0..newline_pos]) &&
             is_binary_string(stdin_input[newline_pos + 1..binary_end])
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures exists newline_pos :: 0 <= newline_pos < |stdin_input| && stdin_input[newline_pos] == '\n' &&
            newline_pos + 1 < |stdin_input| &&
            exists binary_end :: newline_pos + 1 <= binary_end <= |stdin_input| &&
            (binary_end == |stdin_input| || stdin_input[binary_end] == '\n') &&
            is_binary_string(stdin_input[newline_pos + 1..binary_end]) &&
            result == int_to_string(abs_diff_count(stdin_input[newline_pos + 1..binary_end])) + "\n"
// </vc-spec>
// <vc-code>
{
    var newline_pos := find_newline_exists(stdin_input);
    
    assert newline_pos + 1 < |stdin_input|;
    var binary_end := find_binary_end_exists(stdin_input, newline_pos + 1);
    
    var n_str := stdin_input[0..newline_pos];
    var binary_str := stdin_input[newline_pos + 1..binary_end];
    
    assert is_valid_integer(n_str);
    assert is_binary_string(binary_str);
    
    var diff := abs_diff_count(binary_str);
    abs_diff_count_non_negative(binary_str);
    
    var diff_str := int_to_string(diff);
    int_to_string_valid(diff);
    
    result := diff_str + "\n";
}
// </vc-code>

