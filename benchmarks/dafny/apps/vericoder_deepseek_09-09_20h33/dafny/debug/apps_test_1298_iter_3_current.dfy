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
lemma count_char_append(s1: string, s2: string, c: char)
    ensures count_char(s1 + s2, c) == count_char(s1, c) + count_char(s2, c)
{
    if |s1| == 0 {
        // Base case: empty s1
    } else {
        count_char_append(s1[1..], s2, c);
    }
}

lemma count_char_slice(s: string, start: int, end: int, c: char)
    requires 0 <= start <= end <= |s|
    ensures count_char(s[start..end], c) == count_char(s, c) - count_char(s[0..start], c) - count_char(s[end..], c)
{
    calc {
        count_char(s, c);
        == { count_char_append(s[0..start], s[start..], c); }
        count_char(s[0..start], c) + count_char(s[start..], c);
        == { count_char_append(s[start..end], s[end..], c); 
             assert s[start..] == s[start..end] + s[end..]; }
        count_char(s[0..start], c) + count_char(s[start..end], c) + count_char(s[end..], c);
    }
    assert count_char(s[start..end], c) == count_char(s, c) - count_char(s[0..start], c) - count_char(s[end..], c);
}

lemma abs_diff_count_non_negative(s: string)
    requires is_binary_string(s)
    ensures abs_diff_count(s) >= 0
{
}

lemma int_to_string_non_empty(n: int)
    requires n >= 0
    ensures |int_to_string(n)| > 0
{
    if n == 0 {
    } else if n < 10 {
    } else {
        int_to_string_non_empty(n / 10);
    }
}

lemma find_newline_exists(s: string, start: int)
    requires |s| > 0
    requires exists i :: 0 <= i < |s| && s[i] == '\n'
    requires 0 <= start <= |s|
    ensures exists i :: start <= i < |s| && s[i] == '\n'
{
}

lemma binary_string_slice(s: string, start: int, end: int)
    requires is_binary_string(s)
    requires 0 <= start <= end <= |s|
    ensures is_binary_string(s[start..end])
{
    if |s| == 0 {
    } else {
        forall i | 0 <= i < |s[start..end]|
            ensures s[start..end][i] == '0' || s[start..end][i] == '1'
        {
            assert s[start + i] == s[start..end][i];
            assert is_binary_string(s) ==> (s[start + i] == '0' || s[start + i] == '1');
        }
    }
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
    var newline_pos := 0;
    while newline_pos < |stdin_input| && stdin_input[newline_pos] != '\n'
        invariant 0 <= newline_pos <= |stdin_input|
        invariant forall i :: 0 <= i < newline_pos ==> stdin_input[i] != '\n'
    {
        newline_pos := newline_pos + 1;
    }
    assert newline_pos < |stdin_input| && stdin_input[newline_pos] == '\n';
    
    var binary_end := newline_pos + 1;
    while binary_end < |stdin_input| && stdin_input[binary_end] != '\n'
        invariant newline_pos + 1 <= binary_end <= |stdin_input|
        invariant forall i :: newline_pos + 1 <= i < binary_end ==> stdin_input[i] != '\n'
    {
        binary_end := binary_end + 1;
    }
    assert binary_end <= |stdin_input|;
    assert binary_end == |stdin_input| || stdin_input[binary_end] == '\n';
    
    var binary_string := stdin_input[newline_pos + 1..binary_end];
    binary_string_slice(stdin_input, newline_pos + 1, binary_end);
    assert is_binary_string(binary_string);
    var diff := abs_diff_count(binary_string);
    int_to_string_non_empty(diff);
    result := int_to_string(diff) + "\n";
}
// </vc-code>

