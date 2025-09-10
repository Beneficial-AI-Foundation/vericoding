

// <vc-helpers>
lemma MaxExists(s: seq<int>)
    requires |s| > 0
    ensures exists m :: m in s && forall x :: x in s ==> x <= m
{
    if |s| == 1 {
        assert s[0] in s;
        assert forall x :: x in s ==> x <= s[0];
    } else {
        MaxExists(s[..|s|-1]);
        var m1 :| m1 in s[..|s|-1] && forall x :: x in s[..|s|-1] ==> x <= m1;
        if s[|s|-1] >= m1 {
            assert s[|s|-1] in s;
            assert forall x :: x in s ==> x <= s[|s|-1];
        } else {
            assert m1 in s;
            assert forall x :: x in s ==> x <= m1;
        }
    }
}

lemma UniqueElementsInSorted(s: seq<int>, i: int, result: seq<int>)
    requires forall p, q :: 0 <= p < q < |s| ==> s[p] <= s[q]
    requires 0 <= i <= |s|
    requires forall p, q :: 0 <= p < q < |result| ==> result[p] < result[q]
    requires forall x :: x in result ==> x in s[..i]
    requires i > 0 && |result| > 0
    requires result[|result|-1] in s[..i]
    ensures forall x :: x in s[..i] && (|result| == 0 || x > result[|result|-1]) ==> exists j :: 0 <= j < i && s[j] == x
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
        invariant forall x :: x in s[..i] ==> (exists y :: y in result && y == x)
        invariant i > 0 && |result| > 0 ==> result[|result| - 1] in s[..i] && 
                  (forall x :: x in s[..i] ==> x <= result[|result| - 1] || x in result)
    {
        if |result| == 0 || s[i] > result[|result| - 1] {
            result := result + [s[i]];
        }
        i := i + 1;
    }
    
    assert s[..|s|] == s;
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