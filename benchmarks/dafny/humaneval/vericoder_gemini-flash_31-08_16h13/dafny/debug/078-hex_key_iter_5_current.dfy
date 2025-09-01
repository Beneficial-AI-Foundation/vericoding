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
function count_prime_hex_digits_iter_helper(s: seq<char>, index: int, acc: int) : (count : int)
  decreases |s| - index
  ensures index <= |s| ==> count == acc + count_prime_hex_digits_rec(s[index..])
  ensures index > |s| ==> count == acc
{
  if index >= |s| then
    acc
  else if IsPrimeHexDigit(s[index]) then
    count_prime_hex_digits_iter_helper(s, index + 1, acc + 1)
  else
    count_prime_hex_digits_iter_helper(s, index + 1, acc)
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
  var count_prime_digits := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant count_prime_digits == count_prime_hex_digits_rec(s[0..i])
  {
    if IsPrimeHexDigit(s[i])
    {
      count_prime_digits := count_prime_digits + 1;
    }
    i := i + 1;
  }
  return count_prime_digits;
}
// </vc-code>

