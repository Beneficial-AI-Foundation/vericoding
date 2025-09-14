// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fixed helper function for finding first duplicate */
function HasEarlierDuplicate(lst: seq<int>, val: int, end: int): bool
    requires 0 <= end <= |lst|
    decreases end
{
    if end <= 1 then false
    else (exists j :: 0 <= j < end - 1 && lst[j] == val) || HasEarlierDuplicate(lst, val, end - 1)
}

/* helper modified by LLM (iteration 5): Fixed predicate by removing explicit bool return type */
predicate IsEarliestDuplicate(lst: seq<int>, val: int, idx: int)
    requires 0 <= idx < |lst|
    reads *
{
    lst[idx] == val &&
    forall k, l :: 0 <= k < l < |lst| && lst[k] == lst[l] && l <= idx ==> k >= idx
}
// </vc-helpers>

// <vc-spec>
method FirstDuplicate(lst: seq<int>) returns (result: int)
    ensures
        /* if result = -1, then lst does not contain any duplicates */
        (result == -1 ==> forall i, j :: 0 <= i < j < |lst| ==> lst[i] != lst[j]) &&
        /* if result is not -1, then it is the first duplicate in lst */
        (result != -1 ==> 
            exists i, j :: (0 <= i < j < |lst| && lst[i] == lst[j] && lst[i] == result &&
            forall k, l :: 0 <= k < l < |lst| && lst[k] == lst[l] && l <= i ==> k >= i))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Updated iteration and fixed helper compilation issue */
    var i := 0;
    result := -1;
    while i < |lst| && result == -1
        invariant 0 <= i <= |lst|
        invariant result == -1 ==> forall j, k :: 0 <= j < k < i ==> lst[j] != lst[k]
    {
        var j := i + 1;
        while j < |lst| && result == -1
            invariant i + 1 <= j <= |lst|
            invariant result == -1 ==> forall k :: i + 1 <= k < j ==> lst[k] != lst[i]
        {
            if lst[j] == lst[i] && !HasEarlierDuplicate(lst, lst[i], i) {
                result := lst[i];
            }
            j := j + 1;
        }
        i := i + 1;
    }
}
// </vc-code>
