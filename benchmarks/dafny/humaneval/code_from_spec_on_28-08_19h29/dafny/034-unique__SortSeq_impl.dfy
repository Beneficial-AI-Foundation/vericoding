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
// Helper predicate to check if a sequence is sorted
predicate IsSorted(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Helper predicate to check if two sequences are permutations of each other
predicate IsPermutation(s1: seq<int>, s2: seq<int>)
{
    |s1| == |s2| &&
    multiset(s1) == multiset(s2)
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
    ensures IsSorted(sorted)
    ensures |sorted| == |s|
    ensures IsPermutation(sorted, s)
// </vc-spec>
// <vc-code>
{
    var result := s;
    var n := |s|;
    if n <= 1 {
        sorted := s;
        return;
    }
    
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant IsSorted(result[..i])
        invariant IsPermutation(result, s)
    {
        var minIndex := i;
        var j := i + 1;
        while j < n
            invariant i <= j <= n
            invariant i <= minIndex < n
            invariant forall k :: i <= k < j ==> result[minIndex] <= result[k]
            invariant IsPermutation(result, s)
        {
            if result[j] < result[minIndex] {
                minIndex := j;
            }
            j := j + 1;
        }
        if minIndex != i {
            var temp := result[i];
            result := result[i := result[minIndex]];
            result := result[minIndex := temp];
        }
        i := i + 1;
    }
    sorted := result;
    return;
}
// </vc-code>
