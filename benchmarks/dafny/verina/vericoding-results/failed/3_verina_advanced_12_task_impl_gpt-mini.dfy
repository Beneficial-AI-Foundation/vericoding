// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): NoDupBefore predicate to state that there are no duplicates with second index < j */
predicate NoDupBefore(lst: seq<int>, j: int) { forall p,q :: 0 <= p < q < |lst| && q < j ==> lst[p] != lst[q] }
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
  /* code modified by LLM (iteration 5): scan for first duplicate by increasing j from 0 and checking earlier indices; maintain NoDupBefore invariant */
  var n := |lst|;
  result := -1;
  ghost var ai := -1;
  ghost var aj := -1;
  var j := 0;
  while j < n
    invariant 0 <= j <= n
    invariant result == -1 ==> NoDupBefore(lst, j)
  {
    if result != -1 { break; }
    var k := 0;
    while k < j
      invariant 0 <= k <= j
      invariant result == -1
      invariant result == -1 ==> (forall p :: 0 <= p < k ==> lst[p] != lst[j])
    {
      if lst[k] == lst[j] {
        // Before updating result, NoDupBefore(lst, j) holds by the outer invariant (since result == -1)
        assert result == -1 ==> NoDupBefore(lst, j);
        // Establish NoDupBefore(lst, j) concretely for use after changing result
        if result == -1 {
          assert NoDupBefore(lst, j);
        }
        ai := k;
        aj := j;
        result := lst[j];
        assert 0 <= ai < aj < n;
        assert lst[ai] == lst[aj] && lst[ai] == result;
        // NoDupBefore(lst, aj) holds because it held for j before updating result
        assert NoDupBefore(lst, aj);
        break;
      }
      k := k + 1;
    }
    if result != -1 { break; }
    // Having finished the inner loop without finding a match means for all p<j, lst[p] != lst[j]
    assert result == -1 ==> (forall p :: 0 <= p < j ==> lst[p] != lst[j]);
    // Combine with NoDupBefore(lst, j) to obtain NoDupBefore(lst, j+1)
    assert result == -1 ==> NoDupBefore(lst, j+1);
    j := j + 1;
  }
  if result != -1 {
    // We recorded ai, aj when found; verify required properties
    assert 0 <= ai < aj < n;
    assert lst[ai] == lst[aj] && lst[ai] == result;
    assert NoDupBefore(lst, aj);
    // Minimality follows from NoDupBefore(lst, aj) since ai < aj
    assert forall k0,l0 :: 0 <= k0 < l0 < n && lst[k0] == lst[l0] && l0 <= ai ==> k0 >= ai;
  } else {
    // No duplicate found: NoDupBefore(lst, n) holds by the loop invariant
    assert NoDupBefore(lst, n);
    assert forall p,q :: 0 <= p < q < n ==> lst[p] != lst[q];
  }
}

// </vc-code>
