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
lemma RotSymPreservesValidChar(c: char)
  requires 'a' <= c <= 'z'
  ensures 'a' <= rot_sym(c) <= 'z'
{
  // This lemma is automatically proven by the postcondition of rot_sym
}

lemma RotSymAppliedToValidString(s: string)
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
  ensures forall i :: 0 <= i < |s| ==> 'a' <= rot_sym(s[i]) <= 'z'
{
  forall i | 0 <= i < |s|
    ensures 'a' <= rot_sym(s[i]) <= 'z'
  {
    RotSymPreservesValidChar(s[i]);
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def encrypt(str : str) -> str
Create a function encrypt that takes a string as an argument and returns a string encrypted with the alphabet being rotated. The alphabet should be rotated in a manner such that the letters shift down by two multiplied to two places.
*/
// </vc-description>

// <vc-spec>
method encrypt(s: string) returns (result: string)
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
  ensures |result| == |s|
  ensures forall i :: 0 <= i < |s| ==> result[i] == rot_sym(s[i])
  ensures forall i :: 0 <= i < |result| ==> 'a' <= result[i] <= 'z'
// </vc-spec>
// <vc-code>
{
  result := "";
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == rot_sym(s[j])
    invariant forall j :: 0 <= j < |result| ==> 'a' <= result[j] <= 'z'
  {
    var encrypted_char := rot_sym(s[i]);
    result := result + [encrypted_char];
    i := i + 1;
  }
}
// </vc-code>
