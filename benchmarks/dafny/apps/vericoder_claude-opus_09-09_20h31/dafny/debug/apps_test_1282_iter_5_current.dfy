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
function reverse(s: string): string
{
    if |s| == 0 then ""
    else reverse(s[1..]) + [s[0]]
}

function find_char(s: string, c: char, start: nat): int
    requires start <= |s|
    decreases |s| - start
{
    if start >= |s| then -1
    else if s[start] == c then start
    else find_char(s, c, start + 1)
}

function rfind_char(s: string, c: char): int
{
    rfind_char_from(s, c, |s|)
}

function rfind_char_from(s: string, c: char, i: nat): int
    requires i <= |s|
    decreases i
{
    if i == 0 then -1
    else if s[i-1] == c then i - 1
    else rfind_char_from(s, c, i - 1)
}

function count_char(s: string, c: char): nat
{
    if |s| == 0 then 0
    else (if s[0] == c then 1 else 0) + count_char(s[1..], c)
}

function calculate_balance(s: string): nat
{
    calculate_balance_helper(s, 0, 0)
}

function calculate_balance_helper(s: string, index: nat, current_balance: int): nat
    requires index <= |s|
    decreases |s| - index
{
    if index >= |s| then 0
    else
        var new_balance := if s[index] == 'M' then current_balance + 1 else current_balance - 1;
        var penalty := if new_balance < 0 then -new_balance else 0;
        penalty + calculate_balance_helper(s, index + 1, new_balance)
}

function nat_to_string(n: nat): string
{
    if n == 0 then "0"
    else nat_to_string_helper(n)
}

function nat_to_string_helper(n: nat): string
    decreases n
{
    if n == 0 then ""
    else nat_to_string_helper(n / 10) + [digit_to_char(n % 10)]
}

function digit_to_char(d: nat): char
    requires d < 10
{
    (d + '0' as nat) as char
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
    var rev_input := reverse(input);
    var first_f := find_char(rev_input, 'F', 0);

    if first_f == -1 {
        result := "0\n";
    } else {
        assert first_f >= 0;
        if first_f + 1 > |rev_input| {
            result := "0\n";
        } else {
            assert first_f + 1 <= |rev_input|;
            assert first_f + 1 >= 0;
            var first_m_after_f := find_char(rev_input, 'M', (first_f + 1) as nat);
            if first_m_after_f == -1 {
                result := "0\n";
            } else {
                assert first_m_after_f >= 0;
                var last_m := rfind_char(rev_input, 'M');
                if last_m < first_m_after_f {
                    result := "0\n";
                } else {
                    assert last_m >= first_m_after_f;
                    assert first_m_after_f >= 0;
                    assert last_m >= 0;
                    assert last_m < |rev_input|;
                    assert first_m_after_f <= last_m;
                    assert last_m + 1 <= |rev_input|;
                    var substring := rev_input[first_m_after_f..last_m+1];
                    var balance := calculate_balance(substring);
                    var f_count := count_char(substring, 'F');
                    assert first_m_after_f > first_f;
                    assert first_m_after_f >= first_f + 1;
                    assert balance >= 0 && f_count >= 0;
                    assert first_m_after_f - first_f - 1 >= 0;
                    var swap_time := balance + f_count + first_m_after_f - first_f - 1;
                    assert swap_time >= 0;
                    result := nat_to_string(swap_time as nat) + "\n";
                }
            }
        }
    }
}
// </vc-code>

