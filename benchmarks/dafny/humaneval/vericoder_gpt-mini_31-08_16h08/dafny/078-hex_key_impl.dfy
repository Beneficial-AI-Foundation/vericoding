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
  var i := 0;
  count := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant 0 <= count <= |s|
    invariant count <= i
    invariant count + count_prime_hex_digits_rec(s[i..]) == count_prime_hex_digits_rec(s)
    decreases |s| - i
  {
    var inc := if IsPrimeHexDigit(s[i]) then 1 else 0;
    assert count_prime_hex_digits_rec(s[i..]) == inc + count_prime_hex_digits_rec(s[i+1..]);
    assert count + inc + count_prime_hex_digits_rec(s[i+1..]) == count_prime_hex_digits_rec(s);
    count := count + inc;
    i := i + 1;
  }
}
// </vc-code>

