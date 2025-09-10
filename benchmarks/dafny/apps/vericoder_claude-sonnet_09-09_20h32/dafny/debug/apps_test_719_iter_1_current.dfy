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
{
    if n < 10 then [('0' as int + n) as char]
    else int_to_string(n / 10) + [('0' as int + (n % 10)) as char]
}

lemma string_to_int_inverse(n: int)
    requires n >= 0
    ensures string_to_int(int_to_string(n)) == n
{
}

lemma int_to_string_inverse(s: string)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures int_to_string(string_to_int(s)) == s
{
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
    var input_without_newline := stdin_input[..|stdin_input|-1];
    var k := string_to_int(input_without_newline);
    var perfect_num := kth_perfect_number(k);
    result := int_to_string(perfect_num) + "\n";
}
// </vc-code>

