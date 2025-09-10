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
lemma count_prime_hex_digits_rec_append(s: seq<char>, c: char)
    ensures count_prime_hex_digits_rec(s + [c]) == 
            count_prime_hex_digits_rec(s) + (if IsPrimeHexDigit(c) then 1 else 0)
{
    if |s| == 0 {
        assert s + [c] == [c];
        assert count_prime_hex_digits_rec([c]) == (if IsPrimeHexDigit(c) then 1 else 0);
    } else {
        calc {
            count_prime_hex_digits_rec(s + [c]);
            == // by definition of count_prime_hex_digits_rec
            (if IsPrimeHexDigit((s + [c])[0]) then 1 else 0) + count_prime_hex_digits_rec((s + [c])[1..]);
            == { assert (s + [c])[0] == s[0]; assert (s + [c])[1..] == s[1..] + [c]; }
            (if IsPrimeHexDigit(s[0]) then 1 else 0) + count_prime_hex_digits_rec(s[1..] + [c]);
            == { count_prime_hex_digits_rec_append(s[1..], c); }
            (if IsPrimeHexDigit(s[0]) then 1 else 0) + count_prime_hex_digits_rec(s[1..]) + (if IsPrimeHexDigit(c) then 1 else 0);
            == // by definition of count_prime_hex_digits_rec
            count_prime_hex_digits_rec(s) + (if IsPrimeHexDigit(c) then 1 else 0);
        }
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
        invariant count == count_prime_hex_digits_rec(s[0..i])
    {
        var old_count := count;
        
        if IsPrimeHexDigit(s[i]) {
            count := count + 1;
        }
        
        assert s[0..i+1] == s[0..i] + [s[i]];
        count_prime_hex_digits_rec_append(s[0..i], s[i]);
        assert count == old_count + (if IsPrimeHexDigit(s[i]) then 1 else 0);
        assert count == count_prime_hex_digits_rec(s[0..i]) + (if IsPrimeHexDigit(s[i]) then 1 else 0);
        assert count == count_prime_hex_digits_rec(s[0..i+1]);
        
        i := i + 1;
    }
    
    assert s[0..i] == s;
}
// </vc-code>

