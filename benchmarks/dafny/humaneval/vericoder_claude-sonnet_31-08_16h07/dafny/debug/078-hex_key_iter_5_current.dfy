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
lemma count_prime_hex_digits_rec_append(s: seq<char>, i: int)
  requires 0 <= i < |s|
  ensures count_prime_hex_digits_rec(s[..i+1]) == count_prime_hex_digits_rec(s[..i]) + (if IsPrimeHexDigit(s[i]) then 1 else 0)
{
  assert s[..i+1] == s[..i] + [s[i]];
  count_prime_hex_digits_rec_append_helper(s[..i], s[i]);
}

lemma count_prime_hex_digits_rec_append_helper(prefix: seq<char>, c: char)
  ensures count_prime_hex_digits_rec(prefix + [c]) == count_prime_hex_digits_rec(prefix) + (if IsPrimeHexDigit(c) then 1 else 0)
{
  if |prefix| == 0 {
    assert prefix + [c] == [c];
    assert count_prime_hex_digits_rec([c]) == (if IsPrimeHexDigit(c) then 1 else 0) + count_prime_hex_digits_rec([]);
  } else {
    assert prefix + [c] == [prefix[0]] + (prefix[1..] + [c]);
    count_prime_hex_digits_rec_append_helper(prefix[1..], c);
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
    invariant 0 <= count <= i
  {
    if IsPrimeHexDigit(s[i]) {
      count := count + 1;
    }
    i := i + 1;
    count_prime_hex_digits_rec_append(s, i-1);
  }
}
// </vc-code>

