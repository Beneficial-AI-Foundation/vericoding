// <vc-preamble>
// Helper predicate to check if a sequence is sorted in ascending order
ghost predicate IsSorted(s: seq<real>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Helper predicate to check if a sequence has no duplicate elements
ghost predicate IsUnique(s: seq<real>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

// Helper predicate to check if all elements from source appear in target
ghost predicate AllElementsIn(source: seq<real>, target: seq<real>)
{
    forall x :: x in source ==> x in target
}

// Helper predicate to check if all elements in target come from one of the sources
ghost predicate AllElementsFrom(target: seq<real>, source1: seq<real>, source2: seq<real>)
{
    forall x :: x in target ==> x in source1 || x in source2
}

// Method to compute the union of two sequences, returning sorted unique elements
// </vc-preamble>

// <vc-helpers>
// Helper function to check if an element is in a sequence
ghost predicate Contains(s: seq<real>, x: real)
{
    x in s
}

// Helper function to insert an element into a sorted sequence while maintaining sorted order
method InsertSorted(s: seq<real>, x: real) returns (result: seq<real>)
    requires IsSorted(s)
    ensures IsSorted(result)
    ensures |result| == |s| + 1
    ensures x in result
    ensures forall y :: y in s ==> y in result
    ensures forall y :: y in result ==> y == x || y in s
{
    var i := 0;
    while i < |s| && s[i] < x
        invariant 0 <= i <= |s|
        invariant forall j :: 0 <= j < i ==> s[j] < x
    {
        i := i + 1;
    }
    result := s[..i] + [x] + s[i..];
}

/* helper modified by LLM (iteration 5): simplified AddIfNotPresent without duplicate assertions */
// Helper function to add element to sequence if not already present
method AddIfNotPresent(s: seq<real>, x: real) returns (result: seq<real>)
    requires IsSorted(s) && IsUnique(s)
    ensures IsSorted(result)
    ensures IsUnique(result)
    ensures x in result
    ensures forall y :: y in s ==> y in result
    ensures forall y :: y in result ==> y == x || y in s
    ensures |result| <= |s| + 1
    ensures x in s ==> result == s
    ensures x !in s ==> |result| == |s| + 1
{
    if x in s {
        result := s;
    } else {
        result := InsertSorted(s, x);
    }
}
// </vc-helpers>

// <vc-spec>
method Union1d(ar1: seq<real>, ar2: seq<real>) returns (result: seq<real>)
    ensures IsSorted(result)
    ensures IsUnique(result)
    ensures AllElementsIn(ar1, result)
    ensures AllElementsIn(ar2, result)
    ensures AllElementsFrom(result, ar1, ar2)
    ensures |result| <= |ar1| + |ar2|
    ensures forall s :: (IsSorted(s) && IsUnique(s) && 
                        AllElementsIn(ar1, s) && AllElementsIn(ar2, s) && 
                        AllElementsFrom(s, ar1, ar2)) ==> |result| <= |s|
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): simplified implementation without problematic assertions */
    result := [];
    
    // Add all elements from ar1
    var i := 0;
    while i < |ar1|
        invariant 0 <= i <= |ar1|
        invariant IsSorted(result)
        invariant IsUnique(result)
        invariant forall j :: 0 <= j < i ==> ar1[j] in result
        invariant forall x :: x in result ==> x in ar1[..i]
        invariant |result| <= i
    {
        result := AddIfNotPresent(result, ar1[i]);
        i := i + 1;
    }
    
    // Add all elements from ar2
    i := 0;
    while i < |ar2|
        invariant 0 <= i <= |ar2|
        invariant IsSorted(result)
        invariant IsUnique(result)
        invariant AllElementsIn(ar1, result)
        invariant forall j :: 0 <= j < i ==> ar2[j] in result
        invariant forall x :: x in result ==> x in ar1 || x in ar2[..i]
        invariant |result| <= |ar1| + i
    {
        result := AddIfNotPresent(result, ar2[i]);
        i := i + 1;
    }
}
// </vc-code>
