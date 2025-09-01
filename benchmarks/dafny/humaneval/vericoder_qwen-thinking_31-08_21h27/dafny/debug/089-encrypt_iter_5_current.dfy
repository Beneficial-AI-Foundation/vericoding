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
r := "";
for i in 0..|s| {
  invariant r == s[..i].Map(rot_sym).Join("")
  r := r + rot_sym(s[i]);
}
return r;
// </vc-code>

