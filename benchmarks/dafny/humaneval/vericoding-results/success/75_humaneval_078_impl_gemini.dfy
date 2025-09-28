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
/* helper modified by LLM (iteration 5): [retained helper for loop invariant] */
lemma count_prefix_lemma(s: string, i: int)
  requires 0 <= i < |s|
  ensures count_prime_hex_digits(s[..i+1]) == count_prime_hex_digits(s[..i]) + (if is_prime_hex_digit(s[i]) then 1 else 0)
{
  assert s[..i+1] == s[..i] + [s[i]];
  append_count_lemma(s[..i], s[i]);
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
  /* code modified by LLM (iteration 5): [called lemma inside loop to prove invariant] */
  count := 0;
  var i := 0;
  while i < |num|
    invariant 0 <= i <= |num|
    invariant count >= 0
    invariant count <= i
    invariant count == count_prime_hex_digits(num[..i])
  {
    if is_prime_hex_digit(num[i]) {
      count := count + 1;
    }
    count_prefix_lemma(num, i);
    i := i + 1;
  }
  assert num[..|num|] == num;
}
// </vc-code>
