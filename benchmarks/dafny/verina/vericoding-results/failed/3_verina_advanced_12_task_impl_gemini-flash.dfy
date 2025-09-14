// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int {
  if a < b then a else b
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
/* code modified by LLM (iteration 5): Updated the invariant for result to correctly reflect its state throughout the loop. When a duplicate is found, the loop terminates immediately, so the invariant on result needs to capture that `result` is only updated right before returning.  The invariant that `forall k, l :: 0 <= k < l < i && lst[k] == lst[l] ==> false` is only true if no duplicate has been found yet.  The invariant `result == -1` is crucial for the case where no duplicate is found after the loop.*/
{
    var seen: set<int> := {};
    result := -1;
    var i := 0;
    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant forall k, l :: 0 <= k < l < i && lst[k] == lst[l] ==> false // No duplicates found up to index i-1
        invariant forall k :: 0 <= k < i ==> lst[k] in seen
        invariant forall x :: x in seen ==> (exists k :: 0 <= k < i && lst[k] == x)
        invariant result == -1
    {
        if lst[i] in seen {
            result := lst[i];
            return;
        } else {
            seen := seen + {lst[i]};
        }
        i := i + 1;
    }
}
// </vc-code>
