function rot_sym(c: char): char
  // pre-conditions-start
  requires 'a' <= c <= 'z'
  // pre-conditions-end
  // post-conditions-start
  ensures 'a' <= rot_sym(c) <= 'z'
  // post-conditions-end
{
  // impl-start
  var alph := c as int - 'a' as int;
  ((alph + 2 * 2) % 26 + 'a' as int) as char
  // impl-end
}

// <vc-helpers>
function rot_sym(c: char): char
  requires 'a' <= c <= 'z'
  ensures 'a' <= rot_sym(c) <= 'z'
{
  var alph := c as int - 'a' as int;
  ((alph + 4) % 26 + 'a' as int) as char
}
// </vc-helpers>

// <vc-spec>
method encrypt(s: string) returns (r: string)
  // pre-conditions-start
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
  // pre-conditions-end
  // post-conditions-start
  ensures |r| == |s|
  ensures forall i :: 0 <= i < |s| ==> r[i] == rot_sym(s[i])
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var r_seq := new char[|s|];
    for i := 0 to |s| - 1
        invariant 0 <= i <= |s|
        invariant forall k :: 0 <= k < i ==> r_seq[k] == rot_sym(s[k])
    {
        r_seq[i] := rot_sym(s[i]);
    }
    r := new string(r_seq);
}
// </vc-code>

