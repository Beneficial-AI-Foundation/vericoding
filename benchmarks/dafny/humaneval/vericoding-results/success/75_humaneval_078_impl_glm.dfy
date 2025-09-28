// <vc-preamble>

predicate is_hex_char(c: char)
{
    c in "0123456789ABCDEF"
}

predicate is_valid_hex_string(s: string)
{
    forall i :: 0 <= i < |s| ==> is_hex_char(s[i])
}

predicate is_prime_hex_digit(c: char)
{
    c == '2' || c == '3' || c == '5' || c == '7' || c == 'B' || c == 'D'
}

function count_prime_hex_digits(s: string): int
{
    if |s| == 0 then 0
    else (if is_prime_hex_digit(s[0]) then 1 else 0) + count_prime_hex_digits(s[1..])
}
lemma append_count_lemma(s: string, c: char)
    ensures count_prime_hex_digits(s + [c]) == count_prime_hex_digits(s) + (if is_prime_hex_digit(c) then 1 else 0)
{
    if |s| == 0 {
        assert s + [c] == [c];
        assert count_prime_hex_digits([c]) == (if is_prime_hex_digit(c) then 1 else 0) + count_prime_hex_digits([]);
    } else {
        assert s + [c] == [s[0]] + s[1..] + [c];
        assert s + [c] == [s[0]] + (s[1..] + [c]);
        append_count_lemma(s[1..], c);
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added lemma to prove properties of count_prime_hex_digits */
lemma count_prime_hex_digits_properties(s: string)
    ensures count_prime_hex_digits(s) >= 0
    ensures count_prime_hex_digits(s) <= |s|
{
    if |s| == 0 {
        // Base case: automatically satisfied because count_prime_hex_digits(s) = 0
    } else {
        // Recursive case
        // We call the lemma on the substring s[1..]
        count_prime_hex_digits_properties(s[1..]);
        // Now, we break down the current string
        var x := if is_prime_hex_digit(s[0]) then 1 else 0;
        // We know that x is either 0 or 1
        assert 0 <= x <= 1;
        // The definition of the function
        assert count_prime_hex_digits(s) == x + count_prime_hex_digits(s[1..]);
        // From the lemma call, we have:
        assert count_prime_hex_digits(s[1..]) >= 0;
        assert count_prime_hex_digits(s[1..]) <= |s[1..]|;
        // Now, |s[1..]| is |s| - 1
        assert |s[1..]| == |s| - 1;
        // Therefore, we can deduce the two properties for the entire string.
        // For the lower bound: x >=0 and count_prime_hex_digits(s[1..])>=0, so their sum is >=0.
        // For the upper bound: x <=1 and count_prime_hex_digits(s[1..]) <= |s|-1, so the sum <= 1 + (|s|-1) = |s|.
        // We can write:
        assert count_prime_hex_digits(s) >= 0;
        assert count_prime_hex_digits(s) <= |s|;
    }
}
// </vc-helpers>

// <vc-spec>
method hex_key(num: string) returns (count: int)
    requires is_valid_hex_string(num)
    ensures count >= 0
    ensures count <= |num|
    ensures count == count_prime_hex_digits(num)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): call lemma to establish postconditions */
    count_prime_hex_digits_properties(num);
    count := count_prime_hex_digits(num);
}
// </vc-code>
