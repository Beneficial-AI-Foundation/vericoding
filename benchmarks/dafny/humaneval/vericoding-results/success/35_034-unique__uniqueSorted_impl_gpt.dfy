// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate NonDecreasing(s: seq<int>) { forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j] }
predicate StrictlyIncreasing(s: seq<int>) { forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j] }
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
  var res: seq<int> := [];
  var i: int := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall j, k :: 0 <= j < k < |res| ==> res[j] < res[k]
    invariant forall x :: x in res ==> x in s
    invariant forall x :: x in s[..i] ==> x in res
    invariant (i == 0 ==> |res| == 0) && (i > 0 ==> |res| > 0 && res[|res|-1] == s[i-1])
    decreases |s| - i
  {
    if |res| == 0 || s[i] > res[|res|-1] {
      assert s[i] in s;
      res := res + [s[i]];
    } else {
      assert |res| > 0;
      assert i > 0; // from invariant and guard
      assert res[|res|-1] == s[i-1];
      assert 0 < i < |s|;
      assert s[i-1] <= s[i];
      assert s[i] >= res[|res|-1];
      assert s[i] <= res[|res|-1];
      assert s[i] == res[|res|-1];
    }
    i := i + 1;
  }
  result := res;
}
// </vc-code>
