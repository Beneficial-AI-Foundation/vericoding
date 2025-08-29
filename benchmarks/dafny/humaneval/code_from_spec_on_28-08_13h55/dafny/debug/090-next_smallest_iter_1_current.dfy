datatype Option<T> = None | Some(T)
function getVal(mx : Option<int>) : int
    requires mx != None
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>
predicate hasAtLeastTwoDistinct(lst: seq<int>)
{
    exists i, j :: 0 <= i < |lst| && 0 <= j < |lst| && i != j && lst[i] != lst[j]
}

function distinctElements(lst: seq<int>): set<int>
{
    set x | x in lst
}

function smallerElements(lst: seq<int>, x: int): seq<int>
{
    seq i | 0 <= i < |lst| && lst[i] < x :: lst[i]
}

predicate allSame(lst: seq<int>)
{
    forall i, j :: 0 <= i < |lst| && 0 <= j < |lst| ==> lst[i] == lst[j]
}

lemma DistinctElementsLemma(lst: seq<int>)
    ensures hasAtLeastTwoDistinct(lst) <==> |distinctElements(lst)| >= 2
{
}

lemma SmallerElementsAllSame(lst: seq<int>, x: int)
    requires forall y :: y in lst && y < x ==> y == (if exists z :: z in lst && z < x then (var z :| z in lst && z < x; z) else 0)
    ensures allSame(smallerElements(lst, x)) || smallerElements(lst, x) == []
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def next_smallest(lst: List[int]) -> Optional[int]
You are given a list of integers. Write a function next_smallest() that returns the 2nd smallest element of the list. Return None if there is no such element. TODO(George): Remove this when being reviewed The spec is defined as: if result is none there is no second smallest element, which exists in a finite list iff there are at least two distinct elements in the list. If result is some x, then x is the second smallest element of the list, the spec obtains the sublist of elements smaller than the result, and checks that this sublist does not contain two distinct elements (they are all the same).
*/
// </vc-description>

// <vc-code>
method next_smallest(lst: seq<int>) returns (result: Option<int>)
    ensures result == None <==> !hasAtLeastTwoDistinct(lst)
    ensures result != None ==> 
        var x := getVal(result);
        x in lst &&
        (exists y :: y in lst && y < x) &&
        allSame(smallerElements(lst, x)) &&
        smallerElements(lst, x) != []
{
    if |lst| == 0 {
        return None;
    }
    
    var distinct := {};
    var i := 0;
    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant distinct == set x | x in lst[..i]
    {
        distinct := distinct + {lst[i]};
        i := i + 1;
    }
    
    if |distinct| < 2 {
        return None;
    }
    
    var sortedDistinct := [];
    var remaining := distinct;
    
    while |remaining| > 0
        invariant |sortedDistinct| + |remaining| == |distinct|
        invariant forall x :: x in sortedDistinct ==> x in distinct
        invariant forall x :: x in remaining ==> x in distinct
        invariant forall i, j :: 0 <= i < j < |sortedDistinct| ==> sortedDistinct[i] <= sortedDistinct[j]
        invariant forall x, y :: x in sortedDistinct && y in remaining ==> x <= y
        decreases |remaining|
    {
        var minVal :| minVal in remaining && forall x :: x in remaining ==> minVal <= x;
        sortedDistinct := sortedDistinct + [minVal];
        remaining := remaining - {minVal};
    }
    
    if |sortedDistinct| >= 2 {
        return Some(sortedDistinct[1]);
    } else {
        return None;
    }
}
// </vc-code>
