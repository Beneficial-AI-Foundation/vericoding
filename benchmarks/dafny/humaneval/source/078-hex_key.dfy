function IsPrimeHexDigit(c: char): bool
{
  c == '2' || c == '3' || c == '5' || c == '7' || c == 'B' || c == 'D'
}
// pure-end
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
// pure-end
lemma count_prop(s: seq<char>)
    requires |s| > 0
    ensures count_prime_hex_digits_rec(s) == count_prime_hex_digits_rec(s[..|s| - 1]) + (
        if IsPrimeHexDigit(s[ |s| - 1 ]) then 1 else 0
    )
{
    if (|s| > 1) {
        assert (s[1..][..|s[1..]| - 1]) == s[1..|s| - 1];
    }
}
// pure-end
method count_prime_hex_digits(s: seq<char>) returns (count : int)
    // post-conditions-start
    ensures count == count_prime_hex_digits_rec(s)
    ensures 0 <= count <= |s|
    // post-conditions-end
{
    // impl-start
    count := 0;
    var i := 0;
    while(i < |s|)
        // invariants-start
        invariant 0 <= i <= |s|
        invariant count == count_prime_hex_digits_rec(s[..i])
        // invariants-end
    {
        // assert-start
        assert count_prime_hex_digits_rec(s[..i + 1]) == count_prime_hex_digits_rec(s[..i]) + (
            if IsPrimeHexDigit(s[ i ]) then 1 else 0
        ) by {
            assert s[..i+1][..i] == s[..i];
            count_prop(s[..i + 1]);
        }
        // assert-end
        count := count + if IsPrimeHexDigit(s[i]) then 1 else 0;
        i := i + 1;
    }
    assert s[..i] == s; // assert-line
    return count;
    // impl-end
}
