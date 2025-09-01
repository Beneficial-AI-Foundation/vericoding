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
lemma count_prime_hex_digits_rec_properties(num: seq<char>)
  ensures 0 <= count_prime_hex_digits_rec(num) <= |num|
  decreases |num|
{
  if |num| != 0 {
    count_prime_hex_digits_rec_properties(num[1..]);
  }
}

lemma count_prime_hex_digits_rec_append(num: seq<char>, c: char)
  ensures count_prime_hex_digits_rec(num + [c]) == 
          count_prime_hex_digits_rec(num) + (if IsPrimeHexDigit(c) then 1 else 0)
  decreases |num|
{
  if |num| == 0 {
    // Base case is handled by function definition
  } else {
    var head := num[0];
    var tail := num[1..];
    count_prime_hex_digits_rec_append(tail, c);
    // Now we know: count_prime_hex_digits_rec(tail + [c]) == count_prime_hex_digits_rec(tail) + (if IsPrimeHexDigit(c) then 1 else 0)
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
    count_prime_hex_digits_rec_append(s[..i], s[i]);
    assert s[..i] + [s[i]] == s[..i+1];
    if IsPrimeHexDigit(s[i]) {
      count := count + 1;
    } else {
      // Maintain the invariant when s[i] is not a prime hex digit
    }
    i := i + 1;
  }
}
// </vc-code>

