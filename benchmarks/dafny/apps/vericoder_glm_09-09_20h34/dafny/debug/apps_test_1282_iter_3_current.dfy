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

// <vc-helpers>
function digit_to_char(d: int): char
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

function nat_to_string(n: nat): string
    decreases n
{
    if n < 10 then [digit_to_char(n)]
    else nat_to_string(n / 10) + [digit_to_char(n % 10)]
}

function reverse(s: string): string
    decreases |s|
{
    if |s| == 0 then ""
    else reverse(s[1:]) + [s[0]]
}

function find_char(s: string, c: char, start: int): int
    requires 0 <= start
    ensures 0 <= result < |s| ==> (start <= result && s[result] == c)
    ensures result == -1 ==> forall i :: start <= i < |s| ==> s[i] != c
    decreases |s| - start
{
    if start >= |s| then -1
    else if s[start] == c then start
    else find_char(s, c, start + 1)
}

function rfind_char(s: string, c: char): int
    ensures 0 <= result < |s| ==> s[result] == c && forall i :: result < i < |s| ==> s[i] != c
    ensures result == -1 ==> forall i :: 0 <= i < |s| ==> s[i] != c
    decreases |s|
{
    if |s| == 0 then -1
    else
        var index_in_rest := rfind_char(s[0..|s|-1], c);
        if index_in_rest != -1 then index_in_rest
        else if s[|s|-1] == c then |s| - 1
        else -1
}

function count_char(s: string, c: char): nat
    decreases |s|
{
    if |s| == 0 then 0
    else (if s[0] == c then 1 else 0) + count_char(s[1:], c)
}

function calculate_balance(s: string): int
    decreases |s|
{
    if |s| == 0 then 0
    else (if s[0] == 'M' then 1 else if s[0] == 'F' then -1 else 0) + calculate_balance(s[1:])
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures |result| >= 1
    ensures result[|result|-1] == '\n'
    ensures exists val :: val >= 0 && result == nat_to_string(val) + "\n"
    ensures result == nat_to_string(ComputeSwapTime(input)) + "\n"
// </vc-spec>
// <vc-code>
{
    var swap_time := ComputeSwapTime(input);
    result := nat_to_string(swap_time) + "\n";
}
// </vc-code>

