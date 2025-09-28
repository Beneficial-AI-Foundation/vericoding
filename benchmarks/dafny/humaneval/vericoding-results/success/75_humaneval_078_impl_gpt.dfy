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
lemma prefix_append_index(s: string, i: int)
    requires 0 <= i < |s|
    ensures s[..i] + [s[i]] == s[..i+1]
{
    assert s[i..i+1] == [s[i]];
    assert s[..i] + s[i..i+1] == s[..i+1];
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
  var i := 0;
  count := 0;
  while i < |num|
    invariant 0 <= i <= |num|
    invariant 0 <= count <= i
    invariant count == count_prime_hex_digits(num[..i])
    decreases |num| - i
  {
    var inc := if is_prime_hex_digit(num[i]) then 1 else 0;
    prefix_append_index(num, i);
    append_count_lemma(num[..i], num[i]);
    assert count_prime_hex_digits(num[..i+1]) == count_prime_hex_digits(num[..i]) + inc;
    i := i + 1;
    count := count + inc;
    assert 0 <= inc;
    assert inc <= 1;
  }
  assert num[..|num|] == num;
}
// </vc-code>
