Given a string of 'M' (boys) and 'F' (girls), determine how many seconds
it takes for all girls to move to the front of the line. Each second,
all boys immediately in front of girls simultaneously swap positions.

predicate ValidInput(input: string)
{
    |input| >= 1 && forall i :: 0 <= i < |input| ==> input[i] == 'M' || input[i] == 'F'
}

function ComputeSwapTime(input: string): nat
    requires ValidInput(input)
{
    var rev_input := reverse(input);
    var first_f := find_char(rev_input, 'F', 0);
    
    if first_f == -1 then 0
    else
        var first_m_after_f := find_char(rev_input, 'M', first_f + 1);
        if first_m_after_f == -1 then 0
        else
            var last_m := rfind_char(rev_input, 'M');
            if last_m < first_m_after_f then 0
            else
                var substring := rev_input[first_m_after_f..last_m+1];
                var balance := calculate_balance(substring);
                var f_count := count_char(substring, 'F');
                balance + f_count + first_m_after_f - first_f - 1
}

function reverse(s: string): string
    ensures |reverse(s)| == |s|
    ensures forall i :: 0 <= i < |s| ==> reverse(s)[i] == s[|s| - 1 - i]
{
    if |s| == 0 then ""
    else reverse(s[1..]) + [s[0]]
}

function find_char(s: string, c: char, start: int): int
    requires 0 <= start <= |s|
    ensures find_char(s, c, start) == -1 || (start <= find_char(s, c, start) < |s|)
    ensures find_char(s, c, start) != -1 ==> s[find_char(s, c, start)] == c
    ensures find_char(s, c, start) != -1 ==> forall i :: start <= i < find_char(s, c, start) ==> s[i] != c
    decreases |s| - start
{
    if start >= |s| then -1
    else if s[start] == c then start
    else find_char(s, c, start + 1)
}

function rfind_char(s: string, c: char): int
    ensures rfind_char(s, c) == -1 || (0 <= rfind_char(s, c) < |s|)
    ensures rfind_char(s, c) != -1 ==> s[rfind_char(s, c)] == c
    ensures rfind_char(s, c) != -1 ==> forall i :: rfind_char(s, c) < i < |s| ==> s[i] != c
{
    rfind_char_helper(s, c, |s| - 1)
}

function rfind_char_helper(s: string, c: char, pos: int): int
    requires -1 <= pos < |s|
    ensures rfind_char_helper(s, c, pos) == -1 || (0 <= rfind_char_helper(s, c, pos) <= pos)
    ensures rfind_char_helper(s, c, pos) != -1 ==> s[rfind_char_helper(s, c, pos)] == c
    ensures rfind_char_helper(s, c, pos) != -1 ==> forall i :: rfind_char_helper(s, c, pos) < i <= pos ==> s[i] != c
    decreases pos + 1
{
    if pos < 0 then -1
    else if s[pos] == c then pos
    else rfind_char_helper(s, c, pos - 1)
}

function count_char(s: string, c: char): int
    ensures count_char(s, c) >= 0
    ensures count_char(s, c) <= |s|
    decreases |s|
{
    if |s| == 0 then 0
    else (if s[0] == c then 1 else 0) + count_char(s[1..], c)
}

function calculate_balance(s: string): int
    ensures calculate_balance(s) >= 0
{
    calculate_balance_helper(s, 0, 0)
}

function calculate_balance_helper(s: string, pos: int, current_balance: int): int
    requires 0 <= pos <= |s|
    requires current_balance >= 0
    ensures calculate_balance_helper(s, pos, current_balance) >= 0
    decreases |s| - pos
{
    if pos >= |s| then current_balance
    else if s[pos] == 'M' then calculate_balance_helper(s, pos + 1, current_balance + 1)
    else calculate_balance_helper(s, pos + 1, if current_balance > 0 then current_balance - 1 else 0)
}

function nat_to_string(n: nat): string
    ensures n == 0 ==> nat_to_string(n) == "0"
    ensures n > 0 ==> |nat_to_string(n)| >= 1
{
    if n == 0 then "0"
    else nat_to_string_helper(n)
}

function nat_to_string_helper(n: nat): string
    requires n > 0
    ensures |nat_to_string_helper(n)| >= 1
    decreases n
{
    if n < 10 then [char_of_digit(n)]
    else nat_to_string_helper(n / 10) + [char_of_digit(n % 10)]
}

function char_of_digit(d: nat): char
    requires d < 10
    ensures char_of_digit(d) in {'0', '1', '2', '3', '4', '5', '6', '7', '8', '9'}
{
    if d == 0 then '0'
    else if d == 1 then '1'
    else if d == 2 then '2'
    else if d == 3 then '3'
    else if d == 4 then '4'
    else if d == 5 then '5'
    else if d == 6 then '6'
    else if d == 7 then '7'
    else if d == 8 then '8'
    else '9'
}

method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures |result| >= 1
    ensures result[|result|-1] == '\n'
    ensures exists val :: val >= 0 && result == nat_to_string(val) + "\n"
    ensures result == nat_to_string(ComputeSwapTime(input)) + "\n"
{
    var swap_time := ComputeSwapTime(input);
    result := nat_to_string(swap_time) + "\n";
}
