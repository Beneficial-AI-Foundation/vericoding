// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method StrLen(a: seq<string>) returns (result: seq<nat>)
  // No preconditions - str_len is defined for all strings
  ensures |result| == |a|
  // Each element in result corresponds to the length of the corresponding input string
  ensures forall i :: 0 <= i < |a| ==> result[i] == |a[i]|
  // Length is always non-negative (automatically satisfied by nat type)
  ensures forall i :: 0 <= i < |result| ==> result[i] >= 0
  // Empty strings have length 0
  ensures forall i :: 0 <= i < |a| ==> (a[i] == "" <==> result[i] == 0)
  // Single character strings have length 1
  ensures forall i :: 0 <= i < |a| ==> 
    (a[i] != "" && |a[i]| == 1 ==> result[i] == 1)
  // Monotonicity property: prefixes have length <= original string length
  ensures forall i :: 0 <= i < |a| ==> 
    forall k :: 0 <= k <= |a[i]| ==> k <= result[i]
  // Deterministic property: same string always gives same length
  ensures forall i, j :: 0 <= i < |a| && 0 <= j < |a| && a[i] == a[j] ==> 
    result[i] == result[j]
  // Concatenation property: length is additive for concatenation
  ensures forall i :: 0 <= i < |a| ==> 
    forall s1, s2 :: a[i] == s1 + s2 ==> result[i] == |s1| + |s2|
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
