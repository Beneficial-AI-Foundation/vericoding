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
    decreases |s|
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
    if |s| == 0 then -1
    else rfind_char_helper(s, c, |s| - 1)
}

function rfind_char_helper(s: string, c: char, pos: int): int
    requires -1 <= pos < |s|
    decreases pos + 1
{
    if pos < 0 then -1
    else if s[pos] == c then pos
    else rfind_char_helper(s, c, pos - 1)
}

function calculate_balance(s: string): nat
{
    calculate_balance_helper(s, 0, 0)
}

function calculate_balance_helper(s: string, pos: nat, balance: nat): nat
    requires pos <= |s|
    decreases |s| - pos
{
    if pos == |s| then balance
    else if s[pos] == 'M' then calculate_balance_helper(s, pos + 1, balance + 1)
    else calculate_balance_helper(s, pos + 1, if balance > 0 then balance - 1 else 0)
}

function count_char(s: string, c: char): nat
    decreases |s|
{
    if |s| == 0 then 0
    else (if s[0] == c then 1 else 0) + count_char(s[1..], c)
}

function nat_to_string(n: nat): string
    decreases n
{
    if n == 0 then "0"
    else nat_to_string_helper(n)
}

function nat_to_string_helper(n: nat): string
    requires n > 0
    decreases n
{
    if n < 10 then [char_of_digit(n)]
    else nat_to_string_helper(n / 10) + [char_of_digit(n % 10)]
}

function char_of_digit(d: nat): char
    requires d < 10
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

lemma ValidInputHasLength(input: string)
    requires ValidInput(input)
    ensures |input| >= 1
{
}

lemma ReversePreservesLength(s: string)
    ensures |reverse(s)| == |s|
    decreases |s|
{
    if |s| == 0 {
    } else {
        ReversePreservesLength(s[1..]);
    }
}

lemma FindCharBounds(s: string, c: char, start: nat) returns (pos: int)
    requires start <= |s|
    ensures pos == find_char(s, c, start)
    ensures pos == -1 || (start <= pos < |s|)
    decreases |s| - start
{
    if start >= |s| {
        pos := -1;
    } else if s[start] == c {
        pos := start;
    } else {
        pos := FindCharBounds(s, c, start + 1);
    }
}

lemma RFindCharBounds(s: string, c: char) returns (pos: int)
    ensures pos == rfind_char(s, c)
    ensures pos == -1 || (0 <= pos < |s|)
{
    if |s| == 0 {
        pos := -1;
    } else {
        pos := RFindCharHelperBounds(s, c, |s| - 1);
    }
}

lemma RFindCharHelperBounds(s: string, c: char, start_pos: int) returns (pos: int)
    requires -1 <= start_pos < |s|
    ensures pos == rfind_char_helper(s, c, start_pos)
    ensures pos == -1 || (0 <= pos <= start_pos)
    decreases start_pos + 1
{
    if start_pos < 0 {
        pos := -1;
    } else if s[start_pos] == c {
        pos := start_pos;
    } else {
        pos := RFindCharHelperBounds(s, c, start_pos - 1);
    }
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
    ValidInputHasLength(input);
    var rev_input := reverse(input);
    ReversePreservesLength(input);
    
    var first_f := find_char(rev_input, 'F', 0);
    var first_f_pos := FindCharBounds(rev_input, 'F', 0);

    if first_f == -1 {
        result := nat_to_string(0) + "\n";
    } else {
        assert 0 <= first_f < |rev_input|;
        assert first_f + 1 <= |rev_input|;
        
        var first_m_after_f := find_char(rev_input, 'M', first_f + 1);
        var first_m_pos := FindCharBounds(rev_input, 'M', first_f + 1);
        
        if first_m_after_f == -1 {
            result := nat_to_string(0) + "\n";
        } else {
            assert first_f + 1 <= first_m_after_f < |rev_input|;
            
            var last_m := rfind_char(rev_input, 'M');
            var last_m_pos := RFindCharBounds(rev_input, 'M');
            
            if last_m < first_m_after_f {
                result := nat_to_string(0) + "\n";
            } else {
                assert 0 <= last_m < |rev_input|;
                assert first_m_after_f <= last_m;
                assert 0 <= first_m_after_f < |rev_input|;
                assert last_m + 1 <= |rev_input|;
                
                var substring := rev_input[first_m_after_f..last_m+1];
                var balance := calculate_balance(substring);
                var f_count := count_char(substring, 'F');
                
                assert first_m_after_f >= first_f + 1;
                assert first_f >= 0;
                assert first_m_after_f >= 1;
                assert first_m_after_f - first_f - 1 >= 0;
                
                var swap_time := balance + f_count + (first_m_after_f - first_f - 1);
                
                result := nat_to_string(swap_time) + "\n";
            }
        }
    }
}
// </vc-code>

