// <vc-preamble>

predicate is_binary_string(s: string)
{
    forall i :: 0 <= i < |s| ==> s[i] == '0' || s[i] == '1'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): No helpers needed */
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
  /* code modified by LLM (iteration 3): Fixed result string assignment */
  var n := |a|;
  result := "";
  var j := 0;
  while j < n
      invariant 0 <= j <= n
      invariant |result| == j
      invariant forall i :: 0 <= i < j ==> (a[i] == b[i] ==> result[i] == '0') && (a[i] != b[i] ==> result[i] == '1')
      invariant forall i :: 0 <= i < j ==> result[i] == '0' || result[i] == '1'
  {
      result := result + [if a[j] == b[j] then '0' else '1'];
      j := j + 1;
  }
}
// </vc-code>
