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
/* helper modified by LLM (iteration 2): simple predicate to assert all characters are lowercase */
predicate AllLowercase(s: string) { forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z' }
// </vc-helpers>

// <vc-spec>
method decode_shift(s: string) returns (t: string)

  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'

  ensures |s| == |t|
  ensures forall i :: 0 <= i < |s| ==> t[i] == decode_char(s[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implement decoding loop; removed redundant null check to avoid warning */
  var n := |s|;
  var a := new char[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant a.Length == n
    invariant forall j :: 0 <= j < i ==> a[j] == decode_char(s[j])
    decreases n - i
  {
    a[i] := decode_char(s[i]);
    i := i + 1;
  }
  t := a[..];
}
// </vc-code>
