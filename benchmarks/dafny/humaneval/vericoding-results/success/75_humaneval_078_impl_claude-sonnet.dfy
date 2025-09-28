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
/* helper modified by LLM (iteration 3): added bounded count lemma to prove count <= length property */
lemma count_bounded_lemma(s: string)
    ensures count_prime_hex_digits(s) <= |s|
{
    if |s| == 0 {
        assert count_prime_hex_digits(s) == 0;
    } else {
        count_bounded_lemma(s[1..]);
        assert count_prime_hex_digits(s) == (if is_prime_hex_digit(s[0]) then 1 else 0) + count_prime_hex_digits(s[1..]);
        if is_prime_hex_digit(s[0]) {
            assert count_prime_hex_digits(s) == 1 + count_prime_hex_digits(s[1..]);
            assert count_prime_hex_digits(s[1..]) <= |s[1..]|;
            assert |s[1..]| == |s| - 1;
            assert count_prime_hex_digits(s) <= 1 + (|s| - 1) == |s|;
        } else {
            assert count_prime_hex_digits(s) == count_prime_hex_digits(s[1..]);
            assert count_prime_hex_digits(s[1..]) <= |s[1..]|;
            assert |s[1..]| == |s| - 1;
            assert count_prime_hex_digits(s) <= |s| - 1 <= |s|;
        }
    }
}

lemma prefix_count_lemma(s: string, i: int, j: int)
    requires 0 <= i <= j <= |s|
    ensures count_prime_hex_digits(s[..i]) + count_prime_hex_digits(s[i..j]) == count_prime_hex_digits(s[..j])
{
    if i == j {
        assert s[i..j] == [];
        assert count_prime_hex_digits(s[i..j]) == 0;
    } else {
        assert s[..j] == s[..i] + s[i..j];
        var prefix := s[..i];
        var suffix := s[i..j];
        concat_count_lemma(prefix, suffix);
    }
}

lemma concat_count_lemma(s1: string, s2: string)
    ensures count_prime_hex_digits(s1 + s2) == count_prime_hex_digits(s1) + count_prime_hex_digits(s2)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
    } else {
        assert s1 + s2 == [s1[0]] + (s1[1..] + s2);
        concat_count_lemma(s1[1..], s2);
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
  /* code modified by LLM (iteration 3): added bounded count lemma call to prove count <= |num| */
  count := 0;
  var i := 0;
  while i < |num|
    invariant 0 <= i <= |num|
    invariant count >= 0
    invariant count == count_prime_hex_digits(num[..i])
    invariant count <= i
  {
    if is_prime_hex_digit(num[i]) {
      count := count + 1;
    }
    i := i + 1;
    
    // Help prove the invariant
    if i <= |num| {
      assert num[..i] == num[..i-1] + [num[i-1]];
      append_count_lemma(num[..i-1], num[i-1]);
    }
  }
  
  // Final assertion to help prove postcondition
  assert i == |num|;
  assert num[..i] == num;
  count_bounded_lemma(num);
}
// </vc-code>
