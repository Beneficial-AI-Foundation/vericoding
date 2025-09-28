// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method DoubleArrayElements(s: seq<int>) returns (result: seq<int>)
    ensures |result| == |s|
    ensures forall i :: 0 <= i < |s| ==> result[i] == 2 * s[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): [added invariant i <= |s| to fix index out of range] */
  result := [];
  var i := 0;
  while i < |s|
    invariant i <= |s|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == 2 * s[j]
  {
    result := result + [2 * s[i]];
    i := i + 1;
  }
}
// </vc-code>
