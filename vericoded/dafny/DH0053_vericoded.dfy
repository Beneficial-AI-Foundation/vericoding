// <vc-preamble>
function encode_char(c: char): char

  requires 'a' <= c <= 'z'

  ensures 'a' <= encode_char(c) <= 'z'

{

  ((c as int - 'a' as int + 5) % 26 + 'a' as int) as char

}
function decode_char(c: char): char

  requires 'a' <= c <= 'z'

  ensures 'a' <= decode_char(c) <= 'z'
  ensures encode_char(decode_char(c)) == c

{

  ((c as int - 'a' as int - 5) % 26 + 'a' as int) as char

}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method encode_shift(s: string) returns (t: string)

  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'

  ensures |s| == |t|
  ensures forall i :: 0 <= i < |s| ==> t[i] == encode_char(s[i])
// </vc-spec>
// <vc-code>
{
  t := "";
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |t| == i
    invariant forall j :: 0 <= j < i ==> t[j] == encode_char(s[j])
  {
    t := t + [encode_char(s[i])];
    i := i + 1;
  }
}
// </vc-code>
