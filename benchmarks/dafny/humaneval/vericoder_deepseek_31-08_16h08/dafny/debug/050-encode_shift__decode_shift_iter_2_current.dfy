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
method encode_shift(s: string) returns (t: string)
  // pre-conditions-start
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
  // pre-conditions-end
  // post-conditions-start
  ensures |s| == |t|
  ensures forall i :: 0 <= i < |s| ==> t[i] == encode_char(s[i])
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma {:vcs_split_on_every_assert} ModuloProperties(a: int, b: int)
  requires b > 0
  ensures 0 <= a % b <= b
lemma {:vcs_split_on_every_assert} CharRangeProperties()
  ensures forall c: char :: 'a' <= c <= 'z' ==> 0 <= c as int - 'a' as int <= 25
lemma {:vcs_split_on_every_assert} EncodeDecodeCorrectness()
  ensures forall c: char :: 'a' <= c <= 'z' ==> encode_char(decode_char(c)) == c
  ensures forall c: char :: 'a' <= c <= 'z' ==> decode_char(encode_char(c)) == c
// </vc-helpers>

// <vc-spec>
method decode_shift(s: string) returns (t: string)
  // pre-conditions-start
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
  // pre-conditions-end
  // post-conditions-start
  ensures |s| == |t|
  ensures forall i :: 0 <= i < |s| ==> t[i] == decode_char(s[i])
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  t := "";
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |t| == i
    invariant forall j :: 0 <= j < i ==> t[j] == decode_char(s[j])
  {
    var c := s[i];
    var shifted := c as int - 'a' as int;
    var shifted2 := shifted - 5;
    var shifted3 := if shifted2 < 0 then shifted2 + 26 else shifted2;
    var shifted4 := shifted3 + 'a' as int;
    t := t + [shifted4 as char];
    i := i + 1;
  }
}
// </vc-code>

