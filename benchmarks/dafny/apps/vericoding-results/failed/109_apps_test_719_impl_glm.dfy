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
function {:verify} string_to_int(s: string): int
    requires forall i: int :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures string_to_int(s) >= 0
{
    if |s| == 0 then 0
    else 10 * string_to_int(s[..|s|-1]) + (ord(s[|s|-1]) - ord('0'))
}

lemma {:verify} int_to_string_then_string_to_int(k: int)
    requires 1 <= k <= 10000
    ensures string_to_int(int_to_string(k)) == k
{
    if k < 10 {
        calc {
            string_to_int(int_to_string(k));
            { assert int_to_string(k) == [chr(ord('0') + k)]; }
            string_to_int([chr(ord('0') + k)]);
            ord(chr(ord('0') + k)) - ord('0');
            { assert ord(chr(ord('0') + k)) == ord('0') + k; }
            (ord('0') + k) - ord('0');
            k
        };
    } else {
        var last_digit := k % 10;
        var prefix := k / 10;
        calc {
            string_to_int(int_to_string(k));
            { assert int_to_string(k) == int_to_string(prefix) + [chr(ord('0') + last_digit)]; }
            string_to_int(int_to_string(prefix) + [chr(ord('0') + last_digit)]);
            10 * string_to_int(int_to_string(prefix)) + (ord(chr(ord('0') + last_digit)) - ord('0'));
            { int_to_string_then_string_to_int(prefix); }
            10 * prefix + (ord(chr(ord('0') + last_digit)) - ord('0'));
            { assert ord(chr(ord('0') + last_digit)) == ord('0') + last_digit; }
            10 * prefix + ((ord('0') + last_digit) - ord('0'));
            10 * prefix + last_digit;
            k
        };
    }
}

function digit_sum(n: int): int
    requires n > 0
    ensures digit_sum(n) >= 1
{
    if n < 10 then n
    else (n % 10) + digit_sum(n / 10)
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
    var s := stdin_input[..|stdin_input|-1];
    var k := string_to_int(s);
    var n := kth_perfect_number(k);
    result := int_to_string(n) + "\n";
}
// </vc-code>

