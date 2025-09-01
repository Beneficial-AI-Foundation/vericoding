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
method sort(s: seq<int>) returns (sorted: seq<int>)
    ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
    ensures |sorted| == |s|
    ensures multiset(s) == multiset(sorted)
    decreases |s|
{
    if |s| == 0 {
        return [];
    }
    var min := s[0];
    var minIndex := 0;
    for i := 1 to |s|
        invariant 0 <= minIndex < |s|
        invariant min == s[minIndex]
        invariant forall j :: 0 <= j < i ==> min <= s[j]
    {
        if s[i] < min {
            min := s[i];
            minIndex := i;
        }
    }
    var rest := s[..minIndex] + s[minIndex+1..];
    var sortedRest := sort(rest);
    return [min] + sortedRest;
}

method removeDuplicates(s: seq<int>) returns (result: seq<int>)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
{
    if |s| == 0 {
        return [];
    }
    result := [s[0]];
    var i := 1;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall j, k :: 0 <= j < k < |result| ==> result[j] < result[k]
        invariant forall j :: 0 <= j < |result| ==> result[j] in s
        invariant forall j :: 0 <= j < i ==> s[j] in result
        invariant |result| > 0 ==> result[|result|-1] <= s[i]
    {
        if s[i] != result[|result|-1] {
            result := result + [s[i]];
        }
        i := i + 1;
    }
}
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
    var sorted := sort(s);
    result := removeDuplicates(sorted);
    return result;
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