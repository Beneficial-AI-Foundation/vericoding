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
  /* code modified by LLM (iteration 3): [added state and invariant to track index of last unique element] */
  result := [];
  var i := 0;
  var last_idx := -1;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall k, l :: 0 <= k < l < |result| ==> result[k] < result[l]
    invariant forall x :: x in result ==> x in s[..i]
    invariant forall x :: x in s[..i] ==> x in result
    invariant |result| > 0 ==> last_idx >= 0 && last_idx < i && result[|result|-1] == s[last_idx]
  {
    if |result| == 0 || s[i] > result[|result| - 1] {
      result := result + [s[i]];
      last_idx := i;
    }
    i := i + 1;
  }
}
// </vc-code>
