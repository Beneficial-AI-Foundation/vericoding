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
// pure-end
method encrypt(s: string) returns (r: string)
  // pre-conditions-start
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
  // pre-conditions-end
  // post-conditions-start
  ensures |r| == |s|
  ensures forall i :: 0 <= i < |s| ==> r[i] == rot_sym(s[i])
  // post-conditions-end
{
  // impl-start
  r := "";
  var i := 0;
  while i < |s|
    // invariants-start
    invariant 0 <= i <= |s|
    invariant |r| == i
    invariant forall j :: 0 <= j < i ==> r[j] == rot_sym(s[j])
    // invariants-end
  {
    r := r + [rot_sym(s[i])];
    i := i + 1;
  }
  // impl-end
}
