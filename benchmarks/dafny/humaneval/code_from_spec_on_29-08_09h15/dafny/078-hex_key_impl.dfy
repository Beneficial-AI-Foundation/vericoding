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
lemma count_prime_hex_digits_rec_bounds(num: seq<char>)
  ensures 0 <= count_prime_hex_digits_rec(num) <= |num|
{
  if |num| == 0 {
    // Base case is trivial
  } else {
    count_prime_hex_digits_rec_bounds(num[1..]);
  }
}

lemma count_prime_hex_digits_rec_step(s: seq<char>, i: nat)
  requires 0 <= i < |s|
  ensures count_prime_hex_digits_rec(s[..i+1]) == count_prime_hex_digits_rec(s[..i]) + (if IsPrimeHexDigit(s[i]) then 1 else 0)
{
  assert s[..i+1] == s[..i] + [s[i]];
  
  if i == 0 {
    calc {
      count_prime_hex_digits_rec(s[..i+1]);
      == count_prime_hex_digits_rec([s[i]]);
      == (if IsPrimeHexDigit(s[i]) then 1 else 0) + count_prime_hex_digits_rec([]);
      == (if IsPrimeHexDigit(s[i]) then 1 else 0) + 0;
      == (if IsPrimeHexDigit(s[i]) then 1 else 0);
      == count_prime_hex_digits_rec(s[..i]) + (if IsPrimeHexDigit(s[i]) then 1 else 0);
    }
  } else {
    var prefix := s[..i];
    var combined := prefix + [s[i]];
    assert combined == s[..i+1];
    assert |prefix| > 0;
    
    calc {
      count_prime_hex_digits_rec(s[..i+1]);
      == count_prime_hex_digits_rec(combined);
      == (if IsPrimeHexDigit(combined[0]) then 1 else 0) + count_prime_hex_digits_rec(combined[1..]);
    }
    
    assert combined[0] == prefix[0];
    assert combined[1..] == prefix[1..] + [s[i]];
    
    count_prime_hex_digits_rec_step(s[1..], i-1);
    
    calc {
      count_prime_hex_digits_rec(combined[1..]);
      == count_prime_hex_digits_rec(prefix[1..] + [s[i]]);
      == count_prime_hex_digits_rec(prefix[1..]) + (if IsPrimeHexDigit(s[i]) then 1 else 0);
    }
    
    calc {
      count_prime_hex_digits_rec(prefix);
      == (if IsPrimeHexDigit(prefix[0]) then 1 else 0) + count_prime_hex_digits_rec(prefix[1..]);
    }
    
    calc {
      count_prime_hex_digits_rec(s[..i+1]);
      == (if IsPrimeHexDigit(combined[0]) then 1 else 0) + count_prime_hex_digits_rec(combined[1..]);
      == (if IsPrimeHexDigit(prefix[0]) then 1 else 0) + count_prime_hex_digits_rec(prefix[1..]) + (if IsPrimeHexDigit(s[i]) then 1 else 0);
      == count_prime_hex_digits_rec(prefix) + (if IsPrimeHexDigit(s[i]) then 1 else 0);
      == count_prime_hex_digits_rec(s[..i]) + (if IsPrimeHexDigit(s[i]) then 1 else 0);
    }
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def hex_key(num: string) -> int
You have been tasked to write a function that receives a hexadecimal number as a string and counts the number of hexadecimal digits that are primes (prime number, or a prime, is a natural number greater than 1 that is not a product of two smaller natural numbers). Hexadecimal digits are 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, A, B, C, D, E, F. Prime numbers are 2, 3, 5, 7, 11, 13, 17,... So you have to determine a number of the following digits: 2, 3, 5, 7, B (=decimal 11), D (=decimal 13). Note: you may assume the input is always correct or empty string, and symbols A,B,C,D,E,F are always uppercase.
*/
// </vc-description>

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
    count_prime_hex_digits_rec_step(s, i);
    
    if IsPrimeHexDigit(s[i]) {
      count := count + 1;
    }
    
    i := i + 1;
  }
  
  assert s[..|s|] == s;
}
// </vc-code>

