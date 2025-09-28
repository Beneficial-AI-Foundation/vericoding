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
/* helper modified by LLM (iteration 2): Added lemma to prove count is bounded by string length */
lemma count_bounded_by_length(s: string)
    ensures count_prime_hex_digits(s) <= |s|
{
    if |s| == 0 {
        assert count_prime_hex_digits(s) == 0;
    } else {
        assert count_prime_hex_digits(s) == (if is_prime_hex_digit(s[0]) then 1 else 0) + count_prime_hex_digits(s[1..]);
        count_bounded_by_length(s[1..]);
        if is_prime_hex_digit(s[0]) {
            assert count_prime_hex_digits(s) == 1 + count_prime_hex_digits(s[1..]) <= 1 + |s[1..]| == |s|;
        } else {
            assert count_prime_hex_digits(s) == count_prime_hex_digits(s[1..]) <= |s[1..]| < |s|;
        }
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
/* code modified by LLM (iteration 2): Added invariant to ensure count stays bounded */
{
  count := 0;
  var i := 0;
  
  while i < |num|
    invariant 0 <= i <= |num|
    invariant count == count_prime_hex_digits(num[..i])
    invariant count <= i
  {
    if is_prime_hex_digit(num[i]) {
      count := count + 1;
    }
    
    assert num[..i+1] == num[..i] + [num[i]];
    append_count_lemma(num[..i], num[i]);
    count_bounded_by_length(num[..i+1]);
    
    i := i + 1;
  }
  
  assert num[..|num|] == num;
  count_bounded_by_length(num);
}
// </vc-code>
