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
/* helper modified by LLM (iteration 2): convert char to single-char string */
function char_to_string(c: char): string {
  [c]
}
// </vc-helpers>

// <vc-spec>
method decode_shift(s: string) returns (t: string)

  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'

  ensures |s| == |t|
  ensures forall i :: 0 <= i < |s| ==> t[i] == decode_char(s[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): use char_to_string helper to append decoded chars */
  var i := 0;
  t := "";
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |t| == i
    invariant forall j :: 0 <= j < i ==> t[j] == decode_char(s[j])
  {
    t := t + char_to_string(decode_char(s[i]));
    i := i + 1;
  }
}
// </vc-code>
