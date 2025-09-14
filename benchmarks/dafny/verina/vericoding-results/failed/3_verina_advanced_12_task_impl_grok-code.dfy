// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
/* code modified by LLM (iteration 5): changed implementation to use a set for tracking seen values, return the first duplicate value when found, else -1 at the end */
var seen: set<int> := {};
var i: int := 0;
while i < |lst|
  invariant 0 <= i <= |lst|
  invariant forall k :: 0 <= k < i ==> lst[k] in seen
  invariant forall x :: x in seen ==> exists k :: 0 <= k < i && lst[k] == x
  decreases |lst| - i
{
  if lst[i] in seen {
    result := lst[i];
    return;
  } else {
    seen := seen + {lst[i]};
  }
  i := i + 1;
}
result := -1;
}
// </vc-code>
