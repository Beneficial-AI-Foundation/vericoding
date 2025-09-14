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
method unique(s: seq<int>) returns (result: seq<int>)
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma InsertSorted(sorted: seq<int>, x: int) returns (result: seq<int>)
    requires forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
    ensures |result| == |sorted| + 1
    ensures multiset(result) == multiset(sorted) + multiset{x}
{
    if |sorted| == 0 {
        result := [x];
    } else if x <= sorted[0] {
        result := [x] + sorted;
    } else if x >= sorted[|sorted| - 1] {
        result := sorted + [x];
    } else {
        var i := 1;
        while i < |sorted| && sorted[i] < x
            invariant 1 <= i <= |sorted|
            invariant forall k :: 0 <= k < i ==> sorted[k] < x
        {
            i := i + 1;
        }
        result := sorted[..i] + [x] + sorted[i..];
    }
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
    sorted := [];
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |sorted| == i
        invariant forall k, j :: 0 <= k < j < |sorted| ==> sorted[k] <= sorted[j]
        invariant multiset(sorted) == multiset(s[..i])
    {
        sorted := InsertSorted(sorted, s[i]);
        i := i + 1;
    }
}
// </vc-code>

