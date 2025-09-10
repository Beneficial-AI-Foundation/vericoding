predicate ValidInput(stdin_input: string)
{
    |stdin_input| > 0 &&
    exists k: int :: k >= 1 && k <= 10000 && stdin_input == int_to_string(k) + "\n"
}

function kth_perfect_number(k: int): int
    requires k >= 1 && k <= 10000
    ensures kth_perfect_number(k) > 0
    ensures digit_sum(kth_perfect_number(k)) == 10
    ensures forall i: int :: 1 <= i < k ==> kth_perfect_number(i) < kth_perfect_number(k)
    ensures forall n: int :: 0 < n < kth_perfect_number(k) && digit_sum(n) == 10 ==> 
        exists j: int :: 1 <= j < k && kth_perfect_number(j) == n
{
    if k == 1 then 19
    else if k == 2 then 28
    else if k == 3 then 37
    else if k == 4 then 46
    else if k == 5 then 55
    else if k == 6 then 64
    else if k == 7 then 73
    else if k == 8 then 82
    else if k == 9 then 91
    else if k == 10 then 109
    else 10 * (k - 9) + 99
}

// <vc-helpers>
function digit_sum(n: int): int
    requires n >= 0
    ensures digit_sum(n) >= 0
{
    if n < 10 then n
    else (n % 10) + digit_sum(n / 10)
}

function string_to_int(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if |s| == 1 then s[0] as int - '0' as int
    else string_to_int(s[..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int)
}

function int_to_string(n: int): string
    requires n >= 0
    ensures |int_to_string(n)| > 0
    ensures forall i :: 0 <= i < |int_to_string(n)| ==> '0' <= int_to_string(n)[i] <= '9'
{
    if n < 10 then [('0' as int + n) as char]
    else int_to_string(n / 10) + [('0' as int + (n % 10)) as char]
}

lemma string_to_int_inverse(n: int)
    requires n >= 0
    ensures string_to_int(int_to_string(n)) == n
{
    if n < 10 {
    } else {
        string_to_int_inverse(n / 10);
    }
}

lemma int_to_string_inverse(s: string)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    requires s[0] != '0' || |s| == 1
    ensures string_to_int(s) >= 0
    ensures int_to_string(string_to_int(s)) == s
{
    if |s| == 1 {
    } else {
        int_to_string_inverse(s[..|s|-1]);
    }
}

lemma digit_sum_properties()
    ensures digit_sum(19) == 10
    ensures digit_sum(28) == 10
    ensures digit_sum(37) == 10
    ensures digit_sum(46) == 10
    ensures digit_sum(55) == 10
    ensures digit_sum(64) == 10
    ensures digit_sum(73) == 10
    ensures digit_sum(82) == 10
    ensures digit_sum(91) == 10
    ensures digit_sum(109) == 10
    ensures forall k {:trigger digit_sum(10 * (k - 9) + 99)} :: k > 10 ==> digit_sum(10 * (k - 9) + 99) == 10
{
    assert digit_sum(19) == 1 + 9 == 10;
    assert digit_sum(28) == 2 + 8 == 10;
    assert digit_sum(37) == 3 + 7 == 10;
    assert digit_sum(46) == 4 + 6 == 10;
    assert digit_sum(55) == 5 + 5 == 10;
    assert digit_sum(64) == 6 + 4 == 10;
    assert digit_sum(73) == 7 + 3 == 10;
    assert digit_sum(82) == 8 + 2 == 10;
    assert digit_sum(91) == 9 + 1 == 10;
    assert digit_sum(109) == digit_sum(10) + 9 == 1 + 0 + 9 == 10;
    
    forall k {:trigger digit_sum(10 * (k - 9) + 99)} | k > 10
        ensures digit_sum(10 * (k - 9) + 99) == 10
    {
        var num := 10 * (k - 9) + 99;
        assert num >= 109;
        assert num % 10 == 9;
        assert num / 10 == k - 9 + 9 == k;
        assert digit_sum(num) == 9 + digit_sum(k);
        assert digit_sum(k) == 1;
    }
}

lemma kth_perfect_ordering()
    ensures forall k {:trigger kth_perfect_number(k)} :: 1 <= k <= 9 ==> 
        forall n :: 0 < n < kth_perfect_number(k) && digit_sum(n) == 10 ==> 
            exists j {:trigger kth_perfect_number(j)} :: 1 <= j < k && kth_perfect_number(j) == n
{
    forall k {:trigger kth_perfect_number(k)} | 1 <= k <= 9
        ensures forall n :: 0 < n < kth_perfect_number(k) && digit_sum(n) == 10 ==> 
            exists j {:trigger kth_perfect_number(j)} :: 1 <= j < k && kth_perfect_number(j) == n
    {
        forall n | 0 < n < kth_perfect_number(k) && digit_sum(n) == 10
            ensures exists j {:trigger kth_perfect_number(j)} :: 1 <= j < k && kth_perfect_number(j) == n
        {
            if k == 1 {
                assert kth_perfect_number(1) == 19;
                assert n < 19 && digit_sum(n) == 10;
                assert false;
            } else {
                if n == 19 && k > 1 { assert kth_perfect_number(1) == 19; }
                if n == 28 && k > 2 { assert kth_perfect_number(2) == 28; }
                if n == 37 && k > 3 { assert kth_perfect_number(3) == 37; }
                if n == 46 && k > 4 { assert kth_perfect_number(4) == 46; }
                if n == 55 && k > 5 { assert kth_perfect_number(5) == 55; }
                if n == 64 && k > 6 { assert kth_perfect_number(6) == 64; }
                if n == 73 && k > 7 { assert kth_perfect_number(7) == 73; }
                if n == 82 && k > 8 { assert kth_perfect_number(8) == 82; }
                if n == 91 && k > 9 { assert kth_perfect_number(9) == 91; }
            }
        }
    }
}

lemma kth_perfect_properties()
    ensures forall k :: k >= 1 && k <= 10000 ==> digit_sum(kth_perfect_number(k)) == 10
    ensures forall k :: 1 <= k <= 9 ==> forall n :: 0 < n < kth_perfect_number(k) && digit_sum(n) == 10 ==> 
        exists j :: 1 <= j < k && kth_perfect_number(j) == n
    ensures forall k :: k == 2 ==> forall n :: 0 < n < kth_perfect_number(k) && digit_sum(n) == 10 ==> 
        exists j :: 1 <= j < k && kth_perfect_number(j) == n
{
    digit_sum_properties();
    kth_perfect_ordering();
}

lemma valid_input_properties(stdin_input: string)
    requires ValidInput(stdin_input)
    ensures exists k: int :: k >= 1 && k <= 10000 && stdin_input == int_to_string(k) + "\n"
    ensures |stdin_input| > 1
    ensures stdin_input[|stdin_input|-1] == '\n'
    ensures forall i :: 0 <= i < |stdin_input|-1 ==> '0' <= stdin_input[i] <= '9'
    ensures stdin_input[0] != '0' || |stdin_input| == 2
{
    var k :| k >= 1 && k <= 10000 && stdin_input == int_to_string(k) + "\n";
    assert |int_to_string(k)| > 0;
    assert |stdin_input| == |int_to_string(k)| + 1;
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures exists k: int :: k >= 1 && k <= 10000 && 
        stdin_input == int_to_string(k) + "\n" &&
        result == int_to_string(kth_perfect_number(k)) + "\n"
    ensures |result| > 0
// </vc-spec>
// <vc-code>
{
    valid_input_properties(stdin_input);
    
    var input_without_newline := stdin_input[..|stdin_input|-1];
    
    assert |input_without_newline| > 0;
    assert forall i :: 0 <= i < |input_without_newline| ==> '0' <= input_without_newline[i] <= '9';
    assert input_without_newline[0] != '0' || |input_without_newline| == 1;
    
    var k := string_to_int(input_without_newline);
    
    assert k >= 1 && k <= 10000 by {
        var k_val :| k_val >= 1 && k_val <= 10000 && stdin_input == int_to_string(k_val) + "\n";
        string_to_int_inverse(k_val);
        assert input_without_newline == int_to_string(k_val);
        assert k == k_val;
    }
    
    kth_perfect_properties();
    
    var perfect_num := kth_perfect_number(k);
    result := int_to_string(perfect_num) + "\n";
}
// </vc-code>

