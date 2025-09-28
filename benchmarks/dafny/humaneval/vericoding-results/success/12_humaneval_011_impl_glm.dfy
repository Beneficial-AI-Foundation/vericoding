// <vc-preamble>

predicate is_binary_string(s: string)
{
    forall i :: 0 <= i < |s| ==> s[i] == '0' || s[i] == '1'
}
// </vc-preamble>

// <vc-helpers>
function char_xor(c1: char, c2: char): char
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
  /* code modified by LLM (iteration 2): fixed string concatenation by converting char to string */
  var i := 0;
  result := "";
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> 
      (a[j] == b[j] ==> result[j] == '0') &&
      (a[j] != b[j] ==> result[j] == '1')
  {
    result := result + [char_xor(a[i], b[i])];
    i := i + 1;
  }
}
// </vc-code>
