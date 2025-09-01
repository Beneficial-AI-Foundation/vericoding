function encode_char(c: char): char
  // pre-conditions-start
  requires 'a' <= c <= 'z'
  // pre-conditions-end
  // post-conditions-start
  ensures 'a' <= encode_char(c) <= 'z'
  // post-conditions-end
{
  // impl-start
  ((c as int - 'a' as int + 5) % 26 + 'a' as int) as char
  // impl-end
}
function decode_char(c: char): char
  // pre-conditions-start
  requires 'a' <= c <= 'z'
  // pre-conditions-end
  // post-conditions-start
  ensures 'a' <= decode_char(c) <= 'z'
  ensures encode_char(decode_char(c)) == c
  // post-conditions-end
{
  // impl-start
  ((c as int - 'a' as int - 5) % 26 + 'a' as int) as char
  // impl-end
}

// <vc-helpers>
lemma mod_helper(x: int, n: int)
  requires n > 0
  ensures (x % n + n) % n == x % n
{
  calc {
    (x % n + n) % n;
    ==  { assert {:split_here} x % n + n == (x % n + n) % n + n * ((x % n + n) / n); }
    (x % n + n) % n;
  }
}

lemma mod_correct(n: int, k: int)
  requires 0 <= k < n
  ensures (k % n + n) % n == k
{
  mod_helper(k, n);
  assert k % n == k;
}

lemma mod_add_correct(n: int, k: int, a: int)
  requires n > 0
  requires 0 <= k < n
  ensures (k + a) % n == (k + a % n) % n
{
  calc {
    (k + a) % n;
    ==  { assert a == n * (a / n) + a % n; }
    (k + n * (a / n) + a % n) % n;
    ==  { assert {:split_here} (k + n * (a / n) + a % n) % n == (k + a % n) % n; }
    (k + a % n) % n;
  }
}

lemma encode_decode_correct(c: char)
  requires 'a' <= c <= 'z'
  ensures encode_char(decode_char(c)) == c
{
  var k := c as int - 'a' as int;
  var decoded_k := (k - 5) % 26;
  var encoded_decoded := (decoded_k + 5) % 26;
  mod_correct(26, decoded_k + 5);
  calc {
    encoded_decoded;
    ==  { assert decoded_k + 5 == (k - 5) % 26 + 5; }
    ((k - 5) % 26 + 5) % 26;
    ==  { assert (k - 5) % 26 == (k + 21) % 26; }
    ((k + 21) % 26 + 5) % 26;
    ==  { mod_add_correct(26, (k + 21) % 26, 5); }
    ((k + 21) % 26 + 5 % 26) % 26;
    ==  { assert 5 % 26 == 5; }
    ((k + 21) % 26 + 5) % 26;
    ==  { assert {:split_here} (k + 21) % 26 + 5 == (k + 26) % 26; }
    k;
  }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method encode_shift(s: string) returns (t: string)
  // pre-conditions-start
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
  // pre-conditions-end
  // post-conditions-start
  ensures |s| == |t|
  ensures forall i :: 0 <= i < |s| ==> t[i] == encode_char(s[i])
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var n := |s|;
  t := new char[n];
  for i := 0 to n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> 'a' <= t[j] <= 'z'
    invariant forall j :: 0 <= j < i ==> t[j] == encode_char(s[j])
  {
    if i < n {
      t[i] := encode_char(s[i]);
    }
  }
}
// </vc-code>

method decode_shift(s: string) returns (t: string)
  // pre-conditions-start
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
  // pre-conditions-end
  // post-conditions-start
  ensures |s| == |t|
  ensures forall i :: 0 <= i < |s| ==> t[i] == decode_char(s[i])
  // post-conditions-end
{
  assume{:axiom} false;
}