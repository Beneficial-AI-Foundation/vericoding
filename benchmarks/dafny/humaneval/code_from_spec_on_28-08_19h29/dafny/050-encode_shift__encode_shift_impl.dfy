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
lemma EncodeDecodeInverse(c: char)
  requires 'a' <= c <= 'z'
  ensures encode_char(decode_char(c)) == c
{
  var d := decode_char(c);
  var e := encode_char(d);
  calc {
    e as int;
    ((d as int - 'a' as int + 5) % 26 + 'a' as int);
    ((((c as int - 'a' as int - 5) % 26 + 'a' as int) - 'a' as int + 5) % 26 + 'a' as int);
    { assert ((c as int - 'a' as int - 5) % 26 + 5) % 26 == (c as int - 'a' as int) % 26; }
    ((c as int - 'a' as int) % 26 + 'a' as int);
    c as int;
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method encode_shift(s: string) returns (t: string)
Encode data. Requires: the condition holds for all values. Ensures: returns the correct size/count; the condition holds for all values.
*/
// </vc-description>

// <vc-spec>
method encode_shift(s: string) returns (t: string)
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
  ensures |s| == |t|
  ensures forall i :: 0 <= i < |s| ==> t[i] == encode_char(s[i])
// </vc-spec>
// <vc-code>
{
  var res := new char[|s|];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < i ==> res[k] == encode_char(s[k])
  {
    res[i] := encode_char(s[i]);
  }
  t := res[..];
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