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
lemma count_prime_hex_digits_rec_slice_property(s: seq<char>, i: int)
  requires 0 <= i < |s|
  ensures count_prime_hex_digits_rec(s[..i+1]) == count_prime_hex_digits_rec(s[..i]) + (if IsPrimeHexDigit(s[i]) then 1 else 0)
{
  if i == 0 {
    assert s[..1] == [s[0]];
    assert s[..0] == [];
  } else {
    assert s[..i+1] == s[..i] + [s[i]];
    count_prime_hex_digits_rec_append(s[..i], [s[i]]);
  }
}

lemma count_prime_hex_digits_rec_append(a: seq<char>, b: seq<char>)
  ensures count_prime_hex_digits_rec(a + b) == count_prime_hex_digits_rec(a) + count_prime_hex_digits_rec(b)
{
  if |a| == 0 {
    assert a + b == b;
  } else {
    assert a + b == [a[0]] + (a[1..] + b);
    count_prime_hex_digits_rec_append(a[1..], b);
  }
}

lemma empty_slice_property(s: seq<char>)
  ensures s[..|s|] == s
{}
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
    count_prime_hex_digits_rec_slice_property(s, i);
    if IsPrimeHexDigit(s[i]) {
      count := count + 1;
    }
    i := i + 1;
  }
  
  empty_slice_property(s);
}
// </vc-code>
