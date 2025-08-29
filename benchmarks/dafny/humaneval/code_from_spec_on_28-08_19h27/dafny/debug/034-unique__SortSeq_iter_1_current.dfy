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
predicate IsPermutation(s1: seq<int>, s2: seq<int>) {
    multiset(s1) == multiset(s2)
}

lemma PermutationPreservesElements(s1: seq<int>, s2: seq<int>)
    requires IsPermutation(s1, s2)
    ensures forall x :: x in s1 <==> x in s2
{
}

lemma SortedProperty(s: seq<int>, i: int, j: int)
    requires forall x, y :: 0 <= x < y < |s| ==> s[x] <= s[y]
    requires 0 <= i < j < |s|
    ensures s[i] <= s[j]
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method SortSeq(s: seq<int>) returns (sorted: seq<int>)
Sort elements. Ensures: the result is sorted according to the ordering relation; returns the correct size/count; returns a sorted permutation of the input.
*/
// </vc-description>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
    ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
    ensures |sorted| == |s|
    ensures IsPermutation(s, sorted)
// </vc-spec>
// <vc-code>
{
    sorted := s;
    var n := |sorted|;
    
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant |sorted| == n
        invariant IsPermutation(s, sorted)
        invariant forall x, y :: 0 <= x < y < i ==> sorted[x] <= sorted[y]
    {
        var minIndex := i;
        var j := i + 1;
        
        while j < n
            invariant i < j <= n
            invariant i <= minIndex < j
            invariant forall k :: i <= k < j ==> sorted[minIndex] <= sorted[k]
        {
            if sorted[j] < sorted[minIndex] {
                minIndex := j;
            }
            j := j + 1;
        }
        
        if minIndex != i {
            var temp := sorted[i];
            sorted := sorted[i := sorted[minIndex]][minIndex := temp];
        }
        
        i := i + 1;
    }
}
// </vc-code>
