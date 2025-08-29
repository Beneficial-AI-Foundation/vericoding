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
    (((c as int - 'a' as int) % 26) + 'a' as int);
    c as int;
  }
}
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
  var res := new char[|s|];
  for i := 0 to |s|
    invariant forall j :: 0 <= j < i ==> res[j] == encode_char(s[j])
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