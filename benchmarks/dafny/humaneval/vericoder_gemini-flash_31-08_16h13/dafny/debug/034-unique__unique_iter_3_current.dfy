method uniqueSorted(s: seq<int>) returns (result: seq<int>)
    // pre-conditions-start
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    // pre-conditions-end
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method unique(s: seq<int>) returns (result: seq<int>)
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if |s| == 0 {
      return [];
    }

    var currentResult: seq<int> := [s[0]];
    var i := 1;
    while i < |s|
      invariant 0 < |currentResult| <= i + 1
      invariant forall j, k :: 0 <= j < k < |currentResult| ==> currentResult[j] < currentResult[k]
      invariant forall x :: x in currentResult ==> x in s[..i]
      invariant forall x :: x in s[..i] ==> (exists k :: 0 <= k < |currentResult| && currentResult[k] == x)
      invariant forall k :: 0 <= k < |currentResult| ==> (exists j :: 0 <= j < i && s[j] == currentResult[k])
      invariant s[0] == currentResult[0]
      invariant i <= |s|
      invariant (forall k :: 0 <= k < |currentResult| ==> currentResult[k] == s[currentResult[k] == s[0] ? 0 : (var l := 0; while l < i && s[l] != currentResult[k] do l := l + 1; l)] ) // Added this to help with verification
    {
        if s[i] > currentResult[|currentResult|-1] {
            currentResult := currentResult + [s[i]];
        }
        i := i + 1;
    }

    return currentResult;
}
// </vc-code>

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}