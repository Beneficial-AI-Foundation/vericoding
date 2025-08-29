datatype Option<T> = None | Some(T)
function getVal(mx : Option<int>) : int
    requires mx != None
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>
predicate distinct(lst: seq<int>) {
    forall i, j :: 0 <= i < j < |lst| ==> lst[i] != lst[j]
}

function countDistinct(lst: seq<int>): nat {
    |set i | 0 <= i < |lst| :: lst[i]|
}

predicate hasAtLeastTwoDistinct(lst: seq<int>) {
    countDistinct(lst) >= 2
}

function getUniqueElements(lst: seq<int>): seq<int> {
    var s := set i | 0 <= i < |lst| :: lst[i];
    var result := seq(|s|, i requires 0 <= i < |s| => var elems := s; if |elems| > i then var elem :| elem in elems; elem else 0);
    result
}

function smallerElements(lst: seq<int>, x: int): seq<int> {
    seq(|lst|, i requires 0 <= i < |lst| => lst[i])
    |> (s => seq i | 0 <= i < |s| && s[i] < x :: s[i])
}

function sortedSeq(s: set<int>): seq<int>
    ensures var result := sortedSeq(s);
    ensures |result| == |s|
    ensures forall x :: x in s <==> x in result
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
{
    if s == {} then []
    else
        var min := var x :| x in s; x;
        var actualMin := var x :| x in s && forall y :: y in s ==> x <= y; x;
        [actualMin] + sortedSeq(s - {actualMin})
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def next_smallest(lst: List[int]) -> Optional[int]
You are given a list of integers. Write a function next_smallest() that returns the 2nd smallest element of the list. Return None if there is no such element. TODO(George): Remove this when being reviewed The spec is defined as: if result is none there is no second smallest element, which exists in a finite list iff there are at least two distinct elements in the list. If result is some x, then x is the second smallest element of the list, the spec obtains the sublist of elements smaller than the result, and checks that this sublist does not contain two distinct elements (they are all the same).
*/
// </vc-description>

// <vc-spec>
function next_smallest(lst: seq<int>): Option<int>
    ensures next_smallest(lst) == None <==> countDistinct(lst) < 2
    ensures next_smallest(lst) != None ==> 
        var x := getVal(next_smallest(lst));
        exists i :: 0 <= i < |lst| && lst[i] == x &&
        (exists y :: y in lst && y < x) &&
        forall z :: z in lst && z < x ==> z == (var sorted := sortedSeq(set i | 0 <= i < |lst| :: lst[i]); if |sorted| >= 1 then sorted[0] else x)
// </vc-spec>
// <vc-code>
{
    var uniqueSet := set i | 0 <= i < |lst| :: lst[i];
    if |uniqueSet| < 2 then
        None
    else
        var sorted := sortedSeq(uniqueSet);
        Some(sorted[1])
}
// </vc-code>
