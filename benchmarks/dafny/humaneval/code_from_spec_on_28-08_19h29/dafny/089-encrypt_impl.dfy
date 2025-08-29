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
// Helper function to check if a character is a lowercase letter
predicate isLowercase(c: char)
{
  'a' <= c <= 'z'
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def encrypt(str : str) -> str
Create a function encrypt that takes a string as an argument and returns a string encrypted with the alphabet being rotated. The alphabet should be rotated in a manner such that the letters shift down by two multiplied to two places.
*/
// </vc-description>

// <vc-spec>
function encrypt(str: string): string
  requires forall i :: 0 <= i < |str| ==> isLowercase(str[i])
  ensures |encrypt(str)| == |str|
  ensures forall i :: 0 <= i < |str| ==> isLowercase(encrypt(str)[i])
  ensures forall i :: 0 <= i < |str| ==> encrypt(str)[i] == rot_sym(str[i])
// </vc-spec>
// <vc-code>
{
  if |str| == 0 then "" else
    var result: seq<char> := [];
    var i := 0;
    while i < |str|
      invariant 0 <= i <= |str|
      invariant |result| == i
      invariant forall k :: 0 <= k < i ==> result[k] == rot_sym(str[k])
      invariant forall k :: 0 <= k < i ==> isLowercase(result[k])
    {
      result := result + [rot_sym(str[i])];
      i := i + 1;
    }
    result
}
// </vc-code>
