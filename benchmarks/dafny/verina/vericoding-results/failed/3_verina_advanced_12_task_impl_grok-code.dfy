// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): no helpers needed */
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
  /* code modified by LLM (iteration 2): Fixed loop syntax, added correct invariants and decreases to pass verification */
  var seen: set<int>;
  seen := {};
  result := -1;
  var i := 0;
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant forall x :: x in seen <==> exists j :: 0 <= j < i && lst[j] == x
    invariant forall j, k :: 0 <= j < k < i ==> lst[j] != lst[k]
    decreases |lst| - i
  {
    if lst[i] in seen {
      result := lst[i];
      return;
    }
    seen := seen + {lst[i]};
    i := i + 1;
  }
}
// </vc-code>
