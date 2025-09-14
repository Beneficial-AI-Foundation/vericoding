// <vc-preamble>
predicate InArray(a: seq<int>, x: int)
{
    exists i :: 0 <= i < |a| && a[i] == x
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Fixed lemma proof for no duplicates postcondition */
function Contains(arr: seq<int>, x: int): bool
{
    exists i :: 0 <= i < |arr| && arr[i] == x
}

function RemoveDuplicatesAndFilter(arr: seq<int>, filter: seq<int>): seq<int>
{
    if |arr| == 0 then []
    else if Contains(filter, arr[0]) then RemoveDuplicatesAndFilter(arr[1..], filter)
    else if Contains(arr[1..], arr[0]) then RemoveDuplicatesAndFilter(arr[1..], filter)
    else [arr[0]] + RemoveDuplicatesAndFilter(arr[1..], filter)
}

lemma RemoveDuplicatesAndFilterInArray(arr: seq<int>, filter: seq<int>)
    ensures forall k :: 0 <= k < |RemoveDuplicatesAndFilter(arr, filter)| ==> InArray(arr, RemoveDuplicatesAndFilter(arr, filter)[k])
{
    if |arr| == 0 {
    } else if Contains(filter, arr[0]) {
        RemoveDuplicatesAndFilterInArray(arr[1..], filter);
    } else if Contains(arr[1..], arr[0]) {
        RemoveDuplicatesAndFilterInArray(arr[1..], filter);
    } else {
        RemoveDuplicatesAndFilterInArray(arr[1..], filter);
    }
}

lemma RemoveDuplicatesAndFilterNotInFilter(arr: seq<int>, filter: seq<int>)
    ensures forall k :: 0 <= k < |RemoveDuplicatesAndFilter(arr, filter)| ==> !InArray(filter, RemoveDuplicatesAndFilter(arr, filter)[k])
{
    if |arr| == 0 {
    } else if Contains(filter, arr[0]) {
        RemoveDuplicatesAndFilterNotInFilter(arr[1..], filter);
    } else if Contains(arr[1..], arr[0]) {
        RemoveDuplicatesAndFilterNotInFilter(arr[1..], filter);
    } else {
        RemoveDuplicatesAndFilterNotInFilter(arr[1..], filter);
    }
}

lemma RemoveDuplicatesAndFilterNoDuplicates(arr: seq<int>, filter: seq<int>)
    ensures forall i, j :: 0 <= i < j < |RemoveDuplicatesAndFilter(arr, filter)| ==> RemoveDuplicatesAndFilter(arr, filter)[i] != RemoveDuplicatesAndFilter(arr, filter)[j]
{
    if |arr| == 0 {
    } else if Contains(filter, arr[0]) {
        RemoveDuplicatesAndFilterNoDuplicates(arr[1..], filter);
    } else if Contains(arr[1..], arr[0]) {
        RemoveDuplicatesAndFilterNoDuplicates(arr[1..], filter);
    } else {
        var rest := RemoveDuplicatesAndFilter(arr[1..], filter);
        var result := [arr[0]] + rest;
        RemoveDuplicatesAndFilterNoDuplicates(arr[1..], filter);
        
        forall i, j | 0 <= i < j < |result|
            ensures result[i] != result[j]
        {
            if i == 0 {
                assert result[0] == arr[0];
                assert result[j] == rest[j-1];
                assert !Contains(arr[1..], arr[0]);
                RemoveDuplicatesAndFilterSubsetLemma(arr[1..], filter, j-1);
            } else {
                assert result[i] == rest[i-1];
                assert result[j] == rest[j-1];
            }
        }
    }
}

lemma RemoveDuplicatesAndFilterSubsetLemma(arr: seq<int>, filter: seq<int>, idx: int)
    requires 0 <= idx < |RemoveDuplicatesAndFilter(arr, filter)|
    ensures InArray(arr, RemoveDuplicatesAndFilter(arr, filter)[idx])
{
    RemoveDuplicatesAndFilterInArray(arr, filter);
}
// </vc-helpers>

// <vc-spec>
method RemoveElements(a: array<int>, b: array<int>) returns (c: array<int>)
    ensures forall k :: 0 <= k < c.Length ==> InArray(a[..], c[k]) && !InArray(b[..], c[k])
    ensures forall i, j :: 0 <= i < j < c.Length ==> c[i] != c[j]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Added proper array length initialization */
{
    var result := RemoveDuplicatesAndFilter(a[..], b[..]);
    c := new int[|result|];
    var i := 0;
    while i < |result|
        invariant 0 <= i <= |result|
        invariant i <= c.Length
        invariant c.Length == |result|
        invariant forall k :: 0 <= k < i ==> c[k] == result[k]
    {
        c[i] := result[i];
        i := i + 1;
    }
    RemoveDuplicatesAndFilterInArray(a[..], b[..]);
    RemoveDuplicatesAndFilterNotInFilter(a[..], b[..]);
    RemoveDuplicatesAndFilterNoDuplicates(a[..], b[..]);
}
// </vc-code>
