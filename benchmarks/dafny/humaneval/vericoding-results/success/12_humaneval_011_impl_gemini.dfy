// <vc-preamble>

predicate is_binary_string(s: string)
{
    forall i :: 0 <= i < |s| ==> s[i] == '0' || s[i] == '1'
}
// </vc-preamble>

// <vc-helpers>
function xor_char(c1: char, c2: char): char
    requires c1 == '0' || c1 == '1'
    requires c2 == '0' || c2 == '1'
{
    if c1 == c2 then '0' else '1'
}
// </vc-helpers>

// <vc-spec>
method string_xor(a: string, b: string) returns (result: string)
    requires |a| == |b|
    requires is_binary_string(a)
    requires is_binary_string(b)
    ensures |result| == |a|
    ensures is_binary_string(result)
    ensures forall i :: 0 <= i < |a| ==> 
        (a[i] == b[i] ==> result[i] == '0') &&
        (a[i] != b[i] ==> result[i] == '1')
// </vc-spec>
// <vc-code>
{
  result := "";
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant is_binary_string(result)
    invariant forall k :: 0 <= k < i ==> 
        (a[k] == b[k] ==> result[k] == '0') &&
        (a[k] != b[k] ==> result[k] == '1')
  {
    var next_char := xor_char(a[i], b[i]);
    result := result + [next_char];
    i := i + 1;
  }
}
// </vc-code>
