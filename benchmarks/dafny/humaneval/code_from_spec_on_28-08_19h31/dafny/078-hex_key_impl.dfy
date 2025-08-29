function IsPrimeHexDigit(c: char): bool
{
  c == '2' || c == '3' || c == '5' || c == '7' || c == 'B' || c == 'D'
}
function count_prime_hex_digits_rec(num: seq<char>) : (count : int)
  // post-conditions-start
  ensures 0 <= count <= |num|
  // post-conditions-end
{
  // impl-start
  if |num| == 0 then 0
  else (if IsPrimeHexDigit(num[0]) then 1 else 0) + count_prime_hex_digits_rec(num[1..])
  // impl-end
}

// <vc-helpers>
lemma count_prime_hex_digits_rec_non_negative(num: seq<char>)
  ensures 0 <= count_prime_hex_digits_rec(num)
{
  if |num| == 0 {
    assert count_prime_hex_digits_rec(num) == 0;
  } else {
    count_prime_hex_digits_rec_non_negative(num[1..]);
    assert 0 <= count_prime_hex_digits_rec(num[1..]);
    assert count_prime_hex_digits_rec(num) == (if IsPrimeHexDigit(num[0]) then 1 else 0) + count_prime_hex_digits_rec(num[1..]);
  }
}

lemma count_prime_hex_digits_rec_bounded(num: seq<char>)
  ensures count_prime_hex_digits_rec(num) <= |num|
{
  if |num| == 0 {
    assert count_prime_hex_digits_rec(num) == 0;
    assert 0 <= |num|;
  } else {
    count_prime_hex_digits_rec_bounded(num[1..]);
    assert count_prime_hex_digits_rec(num[1..]) <= |num[1..]|;
    assert |num[1..]| == |num| - 1;
    assert count_prime_hex_digits_rec(num) == (if IsPrimeHexDigit(num[0]) then 1 else 0) + count_prime_hex_digits_rec(num[1..]);
    assert (if IsPrimeHexDigit(num[0]) then 1 else 0) <= 1;
    assert count_prime_hex_digits_rec(num) <= 1 + (|num| - 1);
    assert count_prime_hex_digits_rec(num) <= |num|;
  }
}

lemma count_prime_hex_digits_rec_prefix(num: seq<char>, i: int)
  requires 0 <= i <= |num|
  ensures count_prime_hex_digits_rec(num[..i]) == (if i == 0 then 0 else count_prime_hex_digits_rec(num[..i-1]) + (if IsPrimeHexDigit(num[i-1]) then 1 else 0))
  ensures count_prime_hex_digits_rec(num[..i]) <= i
{
  if i == 0 {
    assert num[..i] == [];
    assert count_prime_hex_digits_rec([]) == 0;
  } else {
    count_prime_hex_digits_rec_prefix(num, i - 1);
    assert count_prime_hex_digits_rec(num[..i-1]) <= i - 1;
    assert num[..i] == num[..i-1] + [num[i-1]];
    assert count_prime_hex_digits_rec(num[..i]) == count_prime_hex_digits_rec(num[..i-1]) + (if IsPrimeHexDigit(num[i-1]) then 1 else 0);
    assert (if IsPrimeHexDigit(num[i-1]) then 1 else 0) <= 1;
    assert count_prime_hex_digits_rec(num[..i]) <= (i - 1) + 1;
    assert count_prime_hex_digits_rec(num[..i]) <= i;
  }
}
// </vc-helpers>

// <vc-spec>
method count_prime_hex_digits(s: seq<char>) returns (count : int)
    // post-conditions-start
    ensures count == count_prime_hex_digits_rec(s)
    ensures 0 <= count <= |s|
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  count := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant count == count_prime_hex_digits_rec(s[..i])
  {
    if IsPrimeHexDigit(s[i]) {
      count := count + 1;
    }
    i := i + 1;
    count_prime_hex_digits_rec_prefix(s, i);
    assert count == count_prime_hex_digits_rec(s[..i]);
  }
  assert s[..i] == s;
  assert count == count_prime_hex_digits_rec(s);
}
// </vc-code>
