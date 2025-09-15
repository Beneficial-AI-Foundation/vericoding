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

// </vc-helpers>

// <vc-spec>
method encrypt(s: string) returns (r: string)

  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'

  ensures |r| == |s|
  ensures forall i :: 0 <= i < |s| ==> r[i] == rot_sym(s[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed duplicate variable name error by removing local declaration of 'r' and initializing the return variable directly */
  r := [];
  for i: nat := 0 to |s|
    invariant |r| == i
    invariant forall j: nat :: 0 <= j < i ==> r[j] == rot_sym(s[j])
  {
    r := r + [rot_sym(s[i])];
  }
}
// </vc-code>
