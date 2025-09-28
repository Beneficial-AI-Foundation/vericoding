// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SwapFirstAndLast(a: seq<int>) returns (result: seq<int>)
    requires |a| > 0
    ensures |result| == |a|
    ensures result[0] == a[|a| - 1]
    ensures result[|result| - 1] == a[0]
    ensures forall i :: 1 <= i < |result| - 1 ==> result[i] == a[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed slice bounds error by handling length 1 case separately. */
  if |a| == 1 {
    result := a;
  } else {
    result := [a[|a|-1]] + a[1..|a|-1] + [a[0]];
  }
}
// </vc-code>
