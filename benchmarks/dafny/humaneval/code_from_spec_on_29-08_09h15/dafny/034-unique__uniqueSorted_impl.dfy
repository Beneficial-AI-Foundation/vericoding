

// <vc-helpers>
lemma UniquePreservesElements(s: seq<int>, result: seq<int>)
    requires forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    requires forall x :: x in result ==> x in s
    requires forall x :: x in s ==> x in result
    ensures forall x :: x in result <==> x in s
{
}

lemma SortedImpliesUniqueWhenNoDuplicates(s: seq<int>)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
    ensures forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
{
}

lemma NonDecreasingAndNoDuplicatesImpliesStrictlyIncreasing(s: seq<int>)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    requires forall i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j ==> s[i] != s[j]
    ensures forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method uniqueSorted(s: seq<int>) returns (result: seq<int>)
Sort elements. Requires: the condition holds for all values. Ensures: the condition holds for all values; the condition holds for all values; the condition holds for all values.
*/
// </vc-description>

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
    if |s| == 0 {
        result := [];
        return;
    }
    
    result := [s[0]];
    var i := 1;
    
    while i < |s|
        invariant 1 <= i <= |s|
        invariant |result| >= 1
        invariant forall k, l :: 0 <= k < l < |result| ==> result[k] < result[l]
        invariant forall x :: x in result ==> x in s[..i]
        invariant forall x :: x in s[..i] ==> x in result
        invariant result[|result|-1] == s[i-1]
    {
        if s[i] != s[i-1] {
            result := result + [s[i]];
        }
        i := i + 1;
    }
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