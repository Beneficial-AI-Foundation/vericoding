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
// Helper lemma to prove properties of rot_sym if needed
lemma RotSymPreservesRange(c: char)
  requires 'a' <= c <= 'z'
  ensures 'a' <= rot_sym(c) <= 'z'
{
  var alph := c as int - 'a' as int;
  assert 0 <= alph <= 25;
  var new_alph := (alph + 4) % 26;
  assert 0 <= new_alph <= 25;
  assert 'a' as int <= new_alph + 'a' as int <= 'z' as int;
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
  var result := new char[|s|];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < i ==> result[k] == rot_sym(s[k])
  {
    result[i] := rot_sym(s[i]);
  }
  r := result[..];
}
// </vc-code>
