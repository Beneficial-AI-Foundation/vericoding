// <vc-preamble>
function rot_sym(c: char): char

  requires 'a' <= c <= 'z'

  ensures 'a' <= rot_sym(c) <= 'z'

{

  var alph := c as int - 'a' as int;
  ((alph + 2 * 2) % 26 + 'a' as int) as char

}
// </vc-preamble>

// <vc-helpers>
predicate LowercaseString(s: string) { forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z' }
lemma RotSymPreservesRange(c: char)
  requires 'a' <= c <= 'z'
  ensures 'a' <= rot_sym(c) <= 'z'
{ }
// </vc-helpers>

// <vc-spec>
method encrypt(s: string) returns (r: string)

  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'

  ensures |r| == |s|
  ensures forall i :: 0 <= i < |s| ==> r[i] == rot_sym(s[i])
// </vc-spec>
// <vc-code>
{
  var n := |s|;
  var acc := s[0..0];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |acc| == i
    invariant forall j :: 0 <= j < i ==> acc[j] == rot_sym(s[j])
  {
    var one := s[i..i+1];
    one := one[0 := rot_sym(s[i])];
    acc := acc + one;
    i := i + 1;
  }
  r := acc;
}
// </vc-code>
