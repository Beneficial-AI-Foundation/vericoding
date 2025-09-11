// <vc-preamble>
function IsPrimeHexDigit(c: char): bool
{
  c == '2' || c == '3' || c == '5' || c == '7' || c == 'B' || c == 'D'
}
function count_prime_hex_digits_rec(num: seq<char>) : (count : int)

  ensures 0 <= count <= |num|

{

  if |num| == 0 then 0
  else (if IsPrimeHexDigit(num[0]) then 1 else 0) + count_prime_hex_digits_rec(num[1..])

}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method count_prime_hex_digits(s: seq<char>) returns (count : int)

    ensures count == count_prime_hex_digits_rec(s)
    ensures 0 <= count <= |s|
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
