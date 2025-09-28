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
  /* code modified by LLM (iteration 2): Added loop invariants to prove postconditions */
  var result: seq<char> := [];
  var i := 0;
  while i < |s|
    decreases |s| - i
    invariant 0 <= i <= |s|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == encode_char(s[j])
  {
    result := result + [encode_char(s[i])];
    i := i + 1;
  }
  t := result;
}
// </vc-code>
