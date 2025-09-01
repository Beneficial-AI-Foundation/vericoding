

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
        var m1 :| m1 in s[..|s|-1] && forall x {:trigger x in s[..|s|-1]} :: x in s[..|s|-1] ==> x <= m1;
        if s[|s|-1] >= m1 {
            assert s[|s|-1] in s;
            // For any x in s, either x is in s[..|s|-1] (so x <= m1 <= s[|s|-1]) or x == s[|s|-1]
            assert forall x :: x in s[..|s|-1] ==> x <= m1 <= s[|s|-1];
            assert forall x :: x in s ==> x in s[..|s|-1] || x == s[|s|-1];
            assert forall x :: x in s ==> x <= s[|s|-1];
        } else {
            assert m1 in s[..|s|-1];
            assert m1 in s;
            // For any x in s, either x is in s[..|s|-1] (so x <= m1) or x == s[|s|-1] < m1
            assert forall x :: x in s[..|s|-1] ==> x <= m1;
            assert s[|s|-1] < m1;
            assert forall x :: x in s ==> x in s[..|s|-1] || x == s[|s|-1];
            assert forall x :: x in s ==> x <= m1;
        }
    }
}

lemma SortedDuplicatesAdjacent(s: seq<int>, x: int, i: int, j: int)
    requires forall p, q :: 0 <= p < q < |s| ==> s[p] <= s[q]
    requires 0 <= i < |s| && 0 <= j < |s|
    requires s[i] == x && s[j] == x
    requires i < j
    ensures forall k :: i <= k <= j ==> s[k] == x
    decreases j - i
{
    if i + 1 <= j {
        assert s[i] <= s[i+1] && s[i+1] <= s[j];
        assert s[i] == x && s[j] == x;
        assert s[i+1] == x;
        if i + 1 < j {
            SortedDuplicatesAdjacent(s, x, i+1, j);
        }
    }
}

lemma SortedUniqueElements(s: seq<int>, i: int, x: int)
    requires forall p, q :: 0 <= p < q < |s| ==> s[p] <= s[q]
    requires 0 <= i < |s|
    requires x in s[..i+1]
    ensures exists j :: 0 <= j <= i && s[j] == x
{
    if x == s[i] {
        assert s[i] == x;
    } else {
        assert x in s[..i];
        SortedUniqueElements(s, i-1, x);
    }
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
        invariant forall x :: x in s[..i] ==> exists j :: 0 <= j < |result| && result[j] == x
        invariant i > 0 && |result| > 0 ==> result[|result| - 1] <= s[i-1]
        invariant i > 0 && |result| > 0 ==> result[|result| - 1] in s[..i]
    {
        if |result| == 0 || s[i] > result[|result| - 1] {
            result := result + [s[i]];
            
            // Prove that all elements in s[..i+1] are now in result
            assert forall x :: x in s[..i] ==> exists j :: 0 <= j < |result|-1 && result[j] == x;
            assert s[i] == result[|result|-1];
            assert forall x :: x in s[..i+1] ==> x in s[..i] || x == s[i];
            assert forall x :: x in s[..i+1] ==> exists j :: 0 <= j < |result| && result[j] == x;
        } else {
            // s[i] <= result[|result| - 1], and since result is strictly increasing,
            // s[i] must already be in result
            assert s[i] <= result[|result| - 1];
            
            // Since the sequence is sorted and result contains unique elements from s[..i]
            // in strictly increasing order, s[i] must already be in result
            var j := 0;
            while j < |result| && result[j] < s[i]
                invariant 0 <= j <= |result|
                invariant forall k :: 0 <= k < j ==> result[k] < s[i]
            {
                j := j + 1;
            }
            
            if j < |result| {
                assert result[j] >= s[i];
                if j > 0 {
                    assert result[j-1] < s[i] <= result[j];
                }
                assert s[i] == result[j];  // Must be equal since s[i] is in s[..i+1]
            }
            
            assert exists j :: 0 <= j < |result| && result[j] == s[i];
            assert forall x :: x in s[..i+1] ==> exists j :: 0 <= j < |result| && result[j] == x;
        }
        i := i + 1;
    }
    
    assert s[..|s|] == s;
    assert forall x :: x in s ==> exists j :: 0 <= j < |result| && result[j] == x;
    assert forall x :: x in s ==> x in result;
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