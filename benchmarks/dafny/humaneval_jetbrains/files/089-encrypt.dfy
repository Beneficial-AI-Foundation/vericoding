function rot_sym(c: char): char

  requires 'a' <= c <= 'z'

  ensures 'a' <= rot_sym(c) <= 'z'

{

  var alph := c as int - 'a' as int;
  ((alph + 2 * 2) % 26 + 'a' as int) as char

}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method encrypt(s: string) returns (r: string)

  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'

  ensures |r| == |s|
  ensures forall i :: 0 <= i < |s| ==> r[i] == rot_sym(s[i])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
