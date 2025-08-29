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
    [lst[i] | i in 0..|lst| | lst[i] < x]
}

predicate allSame(lst: seq<int>)
{
    forall i, j :: 0 <= i < |lst| && 0 <= j < |lst| ==> lst[i] == lst[j]
}

lemma DistinctElementsLemma(lst: seq<int>)
    ensures hasAtLeastTwoDistinct(lst) <==> |distinctElements(lst)| >= 2
{
    if hasAtLeastTwoDistinct(lst) {
        assert |distinctElements(lst)| >= 2;
    }
    if |distinctElements(lst)| >= 2 {
        var s := distinctElements(lst);
        var x, y :| x in s && y in s && x != y;
        assert x in lst && y in lst;
        var i, j :| 0 <= i < |lst| && 0 <= j < |lst| && lst[i] == x && lst[j] == y;
        assert hasAtLeastTwoDistinct(lst);
    }
}

lemma SmallerElementsProperty(lst: seq<int>, x: int)
    requires x in lst
    requires exists y :: y in lst && y < x
    requires forall y, z :: y in lst && z in lst && y < x && z < x ==> y == z
    ensures allSame(smallerElements(lst, x)) && smallerElements(lst, x) != []
{
    var smaller := smallerElements(lst, x);
    if |smaller| > 0 {
        var first := smaller[0];
        forall i | 0 <= i < |smaller|
            ensures smaller[i] == first
        {
            assert smaller[i] < x;
            assert first < x;
        }
    }
}

function seqToSet(s: seq<int>): set<int>
{
    set x | x in s
}

lemma SeqToSetCorrectness(s: seq<int>)
    ensures seqToSet(s) == set x | x in s
{
}

function findMin(s: set<int>): int
    requires s != {}
{
    var x :| x in s && forall y :: y in s ==> x <= y; x
}

lemma FindMinCorrectness(s: set<int>)
    requires s != {}
    ensures var m := findMin(s); m in s && forall x :: x in s ==> m <= x
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
    
    var distinct: set<int> := {};
    var i := 0;
    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant distinct == set x | x in lst[..i]
    {
        distinct := distinct + {lst[i]};
        i := i + 1;
    }
    
    DistinctElementsLemma(lst);
    assert distinct == distinctElements(lst);
    
    if |distinct| < 2 {
        return None;
    }
    
    var sortedDistinct: seq<int> := [];
    var remaining := distinct;
    
    while |remaining| > 0
        invariant |sortedDistinct| + |remaining| == |distinct|
        invariant forall x :: x in sortedDistinct ==> x in distinct
        invariant forall x :: x in remaining ==> x in distinct
        invariant forall i, j :: 0 <= i < j < |sortedDistinct| ==> sortedDistinct[i] < sortedDistinct[j]
        invariant forall x, y :: x in sortedDistinct && y in remaining ==> x < y
        invariant seqToSet(sortedDistinct) + remaining == distinct
        decreases |remaining|
    {
        FindMinCorrectness(remaining);
        var minVal := findMin(remaining);
        sortedDistinct := sortedDistinct + [minVal];
        remaining := remaining - {minVal};
    }
    
    if |sortedDistinct| >= 2 {
        var secondSmallest := sortedDistinct[1];
        var smallest := sortedDistinct[0];
        
        assert secondSmallest in distinct;
        assert secondSmallest in lst;
        assert smallest in lst;
        assert smallest < secondSmallest;
        
        assert forall y :: y in lst && y < secondSmallest ==> y == smallest;
        
        SmallerElementsProperty(lst, secondSmallest);
        return Some(secondSmallest);
    } else {
        return None;
    }
}
// </vc-code>
