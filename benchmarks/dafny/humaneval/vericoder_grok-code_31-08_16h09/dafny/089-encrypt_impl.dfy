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
{
  var r_seq: seq<char> := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |r_seq| == i
    invariant forall j :: 0 <= j < i ==> r_seq[j] == rot_sym(s[j])
  {
    var c := s[i];
    var rotated := rot_sym(c);
    r_seq := r_seq + [rotated];
    i := i + 1;
  }
  return r_seq;
}
// </vc-code>

