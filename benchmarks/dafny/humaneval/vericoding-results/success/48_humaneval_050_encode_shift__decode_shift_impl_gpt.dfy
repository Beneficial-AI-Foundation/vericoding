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
function charString(c: char): string
  requires 'a' <= c <= 'z'
  ensures |charString(c)| == 1
  ensures charString(c)[0] == c
{
  if c == 'a' then "a"
  else if c == 'b' then "b"
  else if c == 'c' then "c"
  else if c == 'd' then "d"
  else if c == 'e' then "e"
  else if c == 'f' then "f"
  else if c == 'g' then "g"
  else if c == 'h' then "h"
  else if c == 'i' then "i"
  else if c == 'j' then "j"
  else if c == 'k' then "k"
  else if c == 'l' then "l"
  else if c == 'm' then "m"
  else if c == 'n' then "n"
  else if c == 'o' then "o"
  else if c == 'p' then "p"
  else if c == 'q' then "q"
  else if c == 'r' then "r"
  else if c == 's' then "s"
  else if c == 't' then "t"
  else if c == 'u' then "u"
  else if c == 'v' then "v"
  else if c == 'w' then "w"
  else if c == 'x' then "x"
  else if c == 'y' then "y"
  else if c == 'z' then "z"
  else "a"
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
  var i := 0;
  t := "";
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |t| == i
    invariant forall j :: 0 <= j < i ==> t[j] == decode_char(s[j])
  {
    assert 0 <= i < |s|;
    assert 'a' <= s[i] <= 'z';
    var c := decode_char(s[i]);
    t := t + charString(c);
    i := i + 1;
  }
}
// </vc-code>
