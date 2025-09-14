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
lemma Lemma_CountAdditive(s1: seq<char>, s2: seq<char>)
  ensures count_prime_hex_digits_rec(s1 + s2) == count_prime_hex_digits_rec(s1) + count_prime_hex_digits_rec(s2)
  decreases s1
{
  if |s1| > 0 {
    Lemma_CountAdditive(s1[1..], s2);
  }
}
// </vc-helpers>

// <vc-spec>
method count_prime_hex_digits(s: seq<char>) returns (count : int)

    ensures count == count_prime_hex_digits_rec(s)
    ensures 0 <= count <= |s|
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
  }
}
// </vc-code>
