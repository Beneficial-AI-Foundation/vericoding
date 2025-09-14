// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method uniqueSorted(s: seq<int>) returns (result: seq<int>)

    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]

    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): corrected set conversion and added invariants */
  result := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall k, l :: 0 <= k < l < |result| ==> result[k] < result[l]
    invariant set(result) <= set(s)
    invariant set(s[..i]) <= set(result)
    invariant |result| > 0 ==> result[|result|-1] in set(s[..i])
    decreases |s| - i
  {
    if |result| == 0 || result[|result| - 1] < s[i] {
      result := result + [s[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
