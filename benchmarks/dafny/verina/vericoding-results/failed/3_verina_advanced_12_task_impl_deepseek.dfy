// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed lemma parameter names and ensures clause */
lemma FirstDuplicateLemma(lst: seq<int>, i: int, j: int, result: int)
    requires 0 <= i < j < |lst|
    requires lst[i] == lst[j]
    requires forall k, l :: 0 <= k < l < |lst| && lst[k] == lst[l] && l <= i ==> k >= i
    ensures result != -1 ==> (exists i2, j2 :: 0 <= i2 < j2 < |lst| && lst[i2] == lst[j2] && lst[i2] == result) &&
        (forall k, l :: 0 <= k < l < |lst| && lst[k] == lst[l] && l <= i2 ==> k >= i2)
{
}

predicate NoDuplicatesBefore(lst: seq<int>, index: int)
    requires 0 <= index <= |lst|
{
    forall i, j :: 0 <= i < j < index ==> lst[i] != lst[j]
}

/* helper modified by LLM (iteration 5): Fixed ensures clause to use proper variable names */
function FindFirstDuplicateIndex(lst: seq<int>): (index: int)
    ensures index == -1 ==> forall i, j :: 0 <= i < j < |lst| ==> lst[i] != lst[j]
    ensures index != -1 ==> 0 <= index < |lst| && (exists j :: index < j < |lst| && lst[index] == lst[j]) && NoDuplicatesBefore(lst, index)
{
    if |lst| == 0 then -1
    else
        var rest := lst[1..];
        var candidate := FindFirstDuplicateIndex(rest);
        if candidate == -1 then
            if exists j :: 1 <= j < |lst| && lst[0] == lst[j] then 0 else -1
        else
            if exists j :: 0 <= j < candidate + 1 && lst[j] == lst[0] then
                0
            else
                candidate + 1
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
    /* code modified by LLM (iteration 5): Fixed implementation using helper function */
    var index := FindFirstDuplicateIndex(lst);
    if index == -1 {
        result := -1;
    } else {
        result := lst[index];
    }
}
// </vc-code>
