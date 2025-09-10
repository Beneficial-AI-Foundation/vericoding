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
// pure-end
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
// pure-end
method encode_shift(s: string) returns (t: string)
  // pre-conditions-start
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
  // pre-conditions-end
  // post-conditions-start
  ensures |s| == |t|
  ensures forall i :: 0 <= i < |s| ==> t[i] == encode_char(s[i])
  // post-conditions-end
{
  // impl-start
  t := "";
  var i := 0;
  while i < |s|
    // invariants-start
    invariant 0 <= i <= |s|
    invariant |t| == i
    invariant forall j :: 0 <= j < i ==> t[j] == encode_char(s[j])
    // invariants-end
  {
    t := t + [encode_char(s[i])];
    i := i + 1;
  }
  // impl-end
}

method decode_shift(s: string) returns (t: string)
  // pre-conditions-start
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
  // pre-conditions-end
  // post-conditions-start
  ensures |s| == |t|
  ensures forall i :: 0 <= i < |s| ==> t[i] == decode_char(s[i])
  // post-conditions-end
{
  // impl-start
  t := "";
  var i := 0;
  while i < |s|
    // invariants-start
    invariant 0 <= i <= |s|
    invariant |t| == i
    invariant forall j :: 0 <= j < i ==> t[j] == decode_char(s[j])
    // invariants-end
  {
    t := t + [decode_char(s[i])];
    i := i + 1;
  }
  // impl-end
}
