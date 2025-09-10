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
function find_first_newline(s: string): int
    requires exists i :: 0 <= i < |s| && s[i] == '\n'
    ensures 0 <= find_first_newline(s) < |s|
    ensures s[find_first_newline(s)] == '\n'
    ensures forall i :: 0 <= i < find_first_newline(s) ==> s[i] != '\n'
{
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall j :: 0 <= j < i ==> s[j] != '\n'
    {
        if s[i] == '\n' then
            return i;
        i := i + 1;
    }
    // This should not be reached due to the requires clause
    -1 // Should be unreachable code
}

function find_second_newline_or_end(s: string, start_index: int): int
    requires start_index <= |s| // start_index is usually first_newline_pos + 1
    ensures start_index <= find_second_newline_or_end(s, start_index) <= |s|
    ensures find_second_newline_or_end(s, start_index) == |s| || s[find_second_newline_or_end(s, start_index)] == '\n'
    ensures forall i :: start_index <= i < find_second_newline_or_end(s, start_index) ==> s[i] != '\n'
{
    var i := start_index;
    while i < |s|
        invariant start_index <= i <= |s|
        invariant forall j :: start_index <= j < i ==> s[j] != '\n'
    {
        if s[i] == '\n' then
            return i;
        i := i + 1;
    }
    |s|
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
    var newline_pos := find_first_newline(stdin_input);
    var start_binary_string := newline_pos + 1;
    var end_binary_string := find_second_newline_or_end(stdin_input, start_binary_string);
    
    // Extract the binary string part
    var binary_s := stdin_input[start_binary_string..end_binary_string];

    // Calculate the absolute difference of 0s and 1s
    var diff := abs_diff_count(binary_s);

    // Convert the integer difference to a string
    var diff_str := int_to_string(diff);

    // Form the final result
    result := diff_str + "\n";
}
// </vc-code>

