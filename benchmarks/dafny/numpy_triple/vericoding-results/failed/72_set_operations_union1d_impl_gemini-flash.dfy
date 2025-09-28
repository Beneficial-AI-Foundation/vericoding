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
/* helper modified by LLM (iteration 4): Fixes syntax for iterating over a sequence to build a set. */
function SeqToSet(s: seq<real>): set<real> {
    var res: set<real> := {};
    for i := 0 to |s| - 1 {
        res := res + {s[i]};
    }
    return res;
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
/* code modified by LLM (iteration 4): Initializes min_val using Any() for non-empty sets. */
{
    var set1 := SeqToSet(ar1);
    var set2 := SeqToSet(ar2);
    var unionSet := set1 + set2;

    var currentSet := unionSet;
    result := [];

    while currentSet != {}
        invariant currentSet <= unionSet
        invariant forall x :: x in result ==> x !in currentSet
        invariant IsSorted(result)
        invariant IsUnique(result)
        invariant SeqToSet(result) + currentSet == unionSet
    {
        var min_val: real;

        // Find the minimum value in currentSet
        // Get an arbitrary element to initialize min_val
        min_val := currentSet.Any();

        for x | x in currentSet
        {
            if x < min_val {
                min_val := x;
            }
        }
        
        result := result + [min_val];
        currentSet := currentSet - {min_val};
    }
}
// </vc-code>
