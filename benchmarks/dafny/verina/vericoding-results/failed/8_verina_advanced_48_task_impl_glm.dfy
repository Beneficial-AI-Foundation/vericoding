// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate isSorted(s: seq<int>) {
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

/* helper modified by LLM (iteration 2): changed function method to function */
function Merge(left: seq<int>, right: seq<int>): seq<int>
    requires isSorted(left) && isSorted(right)
    ensures isSorted(Merge(left, right))
    ensures |Merge(left, right)| == |left| + |right|
    ensures multiset(Merge(left, right)) == multiset(left) + multiset(right)
    decreases |left| + |right|
{
    if |left| == 0 then right
    else if |right| == 0 then left
    else
      if left[0] <= right[0] then [left[0]] + Merge(left[1..], right)
      else [right[0]] + Merge(left, right[1..])
}
// </vc-helpers>

// <vc-spec>
method MergeSort(list: seq<int>) returns (result: seq<int>)
    ensures
        |result| == |list| &&
        (forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]) &&
        multiset(result) == multiset(list)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added braces to then branch for consistency */
    if |list| <= 1 then {
        result := list;
    } else {
        var mid := |list| / 2;
        var left := MergeSort(list[0..mid]);
        var right := MergeSort(list[mid..]);
        result := Merge(left, right);
    }
}
// </vc-code>
