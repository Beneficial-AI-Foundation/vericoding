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
// No helpers needed beyond the provided functions, which are already defined outside this block.
// The DAFNY file provided in the prompt had duplicate function definitions.
// The functions IsPrimeHexDigit and count_prime_hex_digits_rec are defined once in the PREAMBLE.
// Therefore, the <vc-helpers> section should be empty to avoid duplicate definition errors.
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
  var count_digits := 0; // Renamed to avoid duplicate local-variable name error
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant count_digits == count_prime_hex_digits_rec(s[..i])
    invariant 0 <= count_digits <= i
  {
    if IsPrimeHexDigit(s[i]) {
      count_digits := count_digits + 1;
    }
    i := i + 1;
  }
  return count_digits;
}
// </vc-code>

