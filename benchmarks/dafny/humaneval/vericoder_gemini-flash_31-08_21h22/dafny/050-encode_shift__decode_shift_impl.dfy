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
function methodShift(s: string, shift_char: char -> char): string
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
  requires forall c :: 'a' <= c <= 'z' ==> 'a' <= shift_char(c) <= 'z'
  ensures |s| == |methodShift(s, shift_char)|
  ensures forall i :: 0 <= i < |s| ==> methodShift(s, shift_char)[i] == shift_char(s[i])
{
  if |s| == 0 then
    ""
  else
    shift_char(s[0]) + methodShift(s[1..], shift_char)
}
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
  var t := methodShift(s, decode_char);
  return t;
}
// </vc-code>

