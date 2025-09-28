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
/* helper modified by LLM (iteration 3): prove bounds on count_prime_hex_digits */
lemma count_bounds(s: string)
  ensures 0 <= count_prime_hex_digits(s) <= |s|
{
  if |s| == 0 {
    // count_prime_hex_digits("") == 0
    assert count_prime_hex_digits(s) == 0;
    assert 0 <= count_prime_hex_digits(s);
    assert count_prime_hex_digits(s) <= |s|;
  } else {
    // s == [s[0]] + s[1..]
    assert s == [s[0]] + s[1..];
    // unfold definition
    assert count_prime_hex_digits(s) == (if is_prime_hex_digit(s[0]) then 1 else 0) + count_prime_hex_digits(s[1..]);
    // apply induction to tail
    count_bounds(s[1..]);
    // from induction: 0 <= count_prime_hex_digits(s[1..]) <= |s[1..]|
    assert 0 <= (if is_prime_hex_digit(s[0]) then 1 else 0) + count_prime_hex_digits(s[1..]);
    assert (if is_prime_hex_digit(s[0]) then 1 else 0) + count_prime_hex_digits(s[1..]) <= 1 + |s[1..]|;
    assert 1 + |s[1..]| == |s|;
    // conclude bounds for s
    assert 0 <= count_prime_hex_digits(s);
    assert count_prime_hex_digits(s) <= |s|;
  }
}

/* helper modified by LLM (iteration 2): prove count_prime_hex_digits distributes over concatenation */
lemma count_concat(a: string, b: string)
  ensures count_prime_hex_digits(a + b) == count_prime_hex_digits(a) + count_prime_hex_digits(b)
{
  if |a| == 0 {
    assert a + b == b;
    assert count_prime_hex_digits(a + b) == count_prime_hex_digits(b);
    assert count_prime_hex_digits(a) == 0;
    assert 0 + count_prime_hex_digits(b) == count_prime_hex_digits(b);
  } else {
    // a = [a[0]] + a[1..]
    assert a == [a[0]] + a[1..];
    // concatenate: a + b == [a[0]] + (a[1..] + b)
    assert a + b == [a[0]] + (a[1..] + b);
    // use definition of count_prime_hex_digits on a + b
    assert count_prime_hex_digits(a + b) == (if is_prime_hex_digit(a[0]) then 1 else 0) + count_prime_hex_digits(a[1..] + b);
    // apply induction to a[1..]
    count_concat(a[1..], b);
    // expand count_prime_hex_digits(a)
    assert count_prime_hex_digits(a) == (if is_prime_hex_digit(a[0]) then 1 else 0) + count_prime_hex_digits(a[1..]);
    // combine equalities
    assert count_prime_hex_digits(a + b) == (if is_prime_hex_digit(a[0]) then 1 else 0) + (count_prime_hex_digits(a[1..]) + count_prime_hex_digits(b));
    assert count_prime_hex_digits(a) + count_prime_hex_digits(b) == (if is_prime_hex_digit(a[0]) then 1 else 0) + (count_prime_hex_digits(a[1..]) + count_prime_hex_digits(b));
    assert (if is_prime_hex_digit(a[0]) then 1 else 0) + (count_prime_hex_digits(a[1..]) + count_prime_hex_digits(b)) == count_prime_hex_digits(a) + count_prime_hex_digits(b);
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
/* code modified by LLM (iteration 3): iterative count with bounds lemma */
{
  var i := 0;
  count := 0;
  while i < |num|
    invariant 0 <= i <= |num|
    invariant 0 <= count <= |num|
    invariant count == count_prime_hex_digits(num[..i])
  {
    var oldi := i;
    var add := (if is_prime_hex_digit(num[i]) then 1 else 0);
    append_count_lemma(num[..i], num[i]);
    count := count + add;
    i := i + 1;
    assert num[..i] == num[..oldi] + [num[oldi]];
    assert count == count_prime_hex_digits(num[..oldi]) + add;
    assert count == count_prime_hex_digits(num[..i]);
    // use bounds lemma to show count stays within limits
    count_bounds(num[..i]);
    assert 0 <= count <= |num[..i]|;
    assert |num[..i]| <= |num|;
  }
  assert num[..|num|] == num;
  assert count == count_prime_hex_digits(num);
}

// </vc-code>
