// <vc-preamble>
/*
 * Dafny specification for numpy.strings.multiply function.
 * Returns element-wise string repetition where each string is repeated
 * the specified number of times. Negative counts are treated as zero.
 */

// Helper function to specify string repetition behavior
function RepeatString(s: string, n: int): string
    decreases if n <= 0 then 0 else n
{
    if n <= 0 then ""
    else if n == 1 then s
    else s + RepeatString(s, n - 1)
}

// Main multiply method specification
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added lemma to prove empty string property */
lemma RepeatEmptyString(s: string, n: int)
  ensures s == "" ==> RepeatString(s, n) == ""
{
  if s == "" {
    if n <= 0 {
      // RepeatString("", n) == "" by definition
    } else if n == 1 {
      // RepeatString("", 1) == "" by definition
    } else {
      // RepeatString("", n) == "" + RepeatString("", n-1)
      // By induction, RepeatString("", n-1) == ""
      // So RepeatString("", n) == "" + "" == ""
    }
  }
}
// </vc-helpers>

// <vc-spec>
method Multiply(a: seq<string>, i: seq<int>) returns (result: seq<string>)
    // Input arrays must have the same length
    requires |a| == |i|
    // Output array has the same length as inputs
    ensures |result| == |a|
    // Core property: Element-wise string repetition
    ensures forall j :: 0 <= j < |result| ==> result[j] == RepeatString(a[j], i[j])
    // Zero/negative repetition property: Always yields empty string
    ensures forall j :: 0 <= j < |result| && i[j] <= 0 ==> result[j] == ""
    // Identity property: Multiplying by 1 yields the original string
    ensures forall j :: 0 <= j < |result| && i[j] == 1 ==> result[j] == a[j]
    // Zero property: Multiplying by 0 yields empty string
    ensures forall j :: 0 <= j < |result| && i[j] == 0 ==> result[j] == ""
    // Empty string property: Empty strings remain empty regardless of repetition
    ensures forall j :: 0 <= j < |result| && a[j] == "" ==> result[j] == ""
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Added lemma call to prove empty string property */
  result := [];
  var idx := 0;
  while idx < |a|
    invariant 0 <= idx <= |a|
    invariant |result| == idx
    invariant forall j :: 0 <= j < idx ==> result[j] == RepeatString(a[j], i[j])
    invariant forall j :: 0 <= j < idx && a[j] == "" ==> result[j] == ""
  {
    RepeatEmptyString(a[idx], i[idx]);
    result := result + [RepeatString(a[idx], i[idx])];
    idx := idx + 1;
  }
}
// </vc-code>
