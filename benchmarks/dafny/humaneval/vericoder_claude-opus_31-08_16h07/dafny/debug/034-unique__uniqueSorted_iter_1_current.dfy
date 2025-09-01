

// <vc-helpers>
lemma InResultImpliesInS(s: seq<int>, result: seq<int>, x: int, i: int)
    requires 0 <= i <= |s|
    requires |result| == 0 || (|result| > 0 && result[|result| - 1] in s[..i])
    requires forall j :: 0 <= j < |result| ==> result[j] in s[..i]
    requires x in result
    ensures x in s
{
    var idx :| 0 <= idx < |result| && result[idx] == x;
    assert result[idx] in s[..i];
    assert x in s;
}

lemma StrictlyIncreasingProperty(result: seq<int>, s: seq<int>, i: int)
    requires forall p, q :: 0 <= p < q < |s| ==> s[p] <= s[q]
    requires 0 <= i <= |s|
    requires |result| > 0
    requires forall p, q :: 0 <= p < q < |result| ==> result[p] < result[q]
    requires forall j :: 0 <= j < |result| - 1 ==> result[j] < result[j + 1]
    ensures forall p, q :: 0 <= p < q < |result| ==> result[p] < result[q]
{
}
// </vc-helpers>

// <vc-spec>
method uniqueSorted(s: seq<int>) returns (result: seq<int>)
    // pre-conditions-start
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    // pre-conditions-end
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    result := [];
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall j, k :: 0 <= j < k < |result| ==> result[j] < result[k]
        invariant forall x :: x in result ==> x in s[..i]
        invariant forall x :: x in s[..i] ==> x in result
        invariant |result| == 0 || result[|result| - 1] == max(s[..i])
    {
        if |result| == 0 || s[i] > result[|result| - 1] {
            result := result + [s[i]];
        }
        i := i + 1;
    }
    
    assert s[..|s|] == s;
}

function max(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else if s[|s| - 1] >= max(s[..|s| - 1]) then s[|s| - 1]
    else max(s[..|s| - 1])
}
// </vc-code>

method unique(s: seq<int>) returns (result: seq<int>)
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
{
  assume{:axiom} false;
}
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}