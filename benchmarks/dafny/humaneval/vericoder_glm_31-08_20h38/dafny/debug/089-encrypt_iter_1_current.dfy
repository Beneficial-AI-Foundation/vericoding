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
// <vc-helpers>

// </vc-helpers>
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
  var seq: seq<char> := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |seq| == i
    invariant forall j :: 0 <= j < i ==> seq[j] == rot_sym(s[j])
  {
    seq := seq + [rot_sym(s[i])];
  }
  r := seq;
}
// </vc-code>

