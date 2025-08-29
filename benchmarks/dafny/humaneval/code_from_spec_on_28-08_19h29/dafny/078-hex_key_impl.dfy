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
// No additional helpers needed beyond what's provided in the preamble.
// </vc-helpers>

// <vc-description>
/*
function_signature: def hex_key(num: string) -> int
You have been tasked to write a function that receives a hexadecimal number as a string and counts the number of hexadecimal digits that are primes (prime number, or a prime, is a natural number greater than 1 that is not a product of two smaller natural numbers). Hexadecimal digits are 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, A, B, C, D, E, F. Prime numbers are 2, 3, 5, 7, 11, 13, 17,... So you have to determine a number of the following digits: 2, 3, 5, 7, B (=decimal 11), D (=decimal 13). Note: you may assume the input is always correct or empty string, and symbols A,B,C,D,E,F are always uppercase.
*/
// </vc-description>

// <vc-spec>
function hex_key(num: string): int
  ensures 0 <= hex_key(num) <= |num|
// </vc-spec>
// <vc-code>
{
  count_prime_hex_digits_rec(num)
}
// </vc-code>
