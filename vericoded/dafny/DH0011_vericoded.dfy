// <vc-preamble>

predicate is_binary_string(s: string)
{
    forall i :: 0 <= i < |s| ==> s[i] == '0' || s[i] == '1'
}
// </vc-preamble>

// <vc-helpers>

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
    invariant forall j :: 0 <= j < i ==>
      (a[j] == b[j] ==> result[j] == '0') &&
      (a[j] != b[j] ==> result[j] == '1')
  {
    if a[i] == b[i] {
      result := result + "0";
    } else {
      result := result + "1";
    }
    i := i + 1;
  }
}
// </vc-code>
