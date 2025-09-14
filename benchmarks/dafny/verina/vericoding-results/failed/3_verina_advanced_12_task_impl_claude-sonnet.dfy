// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate HasDuplicateAt(lst: seq<int>, i: int, j: int)
  requires 0 <= i < j < |lst|
{
  lst[i] == lst[j]
}

predicate IsFirstDuplicate(lst: seq<int>, value: int, firstIdx: int, secondIdx: int)
  requires 0 <= firstIdx < secondIdx < |lst|
{
  lst[firstIdx] == value && lst[secondIdx] == value &&
  forall k, l :: 0 <= k < l < |lst| && lst[k] == lst[l] && l <= firstIdx ==> k >= firstIdx
}

/* helper modified by LLM (iteration 5): fixed lemma to properly handle all cases and match loop invariant structure */
lemma PreserveDuplicateInvariant(lst: seq<int>, i: int)
  requires 0 <= i < |lst|
  requires forall k, l :: 0 <= k < l < |lst| && l < i ==> lst[k] != lst[l]
  requires forall k :: i < k < |lst| ==> lst[i] != lst[k]
  ensures forall k, l :: 0 <= k < l < |lst| && l <= i ==> lst[k] != lst[l]
{
  forall k, l | 0 <= k < l < |lst| && l <= i
    ensures lst[k] != lst[l]
  {
    if l < i {
      // Already ensured by first precondition
    } else {
      // l == i, so we need lst[k] != lst[i] where k < i
      // This follows from the second precondition
      assert lst[k] != lst[i];
    }
  }
}

/* helper modified by LLM (iteration 5): lemma to establish first duplicate property */
lemma EstablishFirstDuplicate(lst: seq<int>, i: int, j: int)
  requires 0 <= i < j < |lst|
  requires lst[i] == lst[j]
  requires forall k, l :: 0 <= k < l < |lst| && l < i ==> lst[k] != lst[l]
  ensures IsFirstDuplicate(lst, lst[i], i, j)
{
  // The key insight: since no duplicates exist before position i,
  // any duplicate involving lst[i] must have i as the first occurrence
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
  /* code modified by LLM (iteration 5): fixed assertion logic and postcondition establishment */
  result := -1;
  var i := 0;
  
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant result == -1 ==> forall k, l :: 0 <= k < l < |lst| && l < i ==> lst[k] != lst[l]
    invariant result != -1 ==> exists k, l :: 0 <= k < l < |lst| && lst[k] == lst[l] && lst[k] == result && IsFirstDuplicate(lst, result, k, l)
  {
    var j := i + 1;
    
    while j < |lst|
      invariant i < j <= |lst|
      invariant result == -1 ==> forall k :: i < k < j ==> lst[i] != lst[k]
      invariant result == -1 ==> forall k, l :: 0 <= k < l < |lst| && l < i ==> lst[k] != lst[l]
      invariant result != -1 ==> exists k, l :: 0 <= k < l < |lst| && lst[k] == lst[l] && lst[k] == result && IsFirstDuplicate(lst, result, k, l)
    {
      if lst[i] == lst[j] {
        result := lst[i];
        EstablishFirstDuplicate(lst, i, j);
        assert IsFirstDuplicate(lst, result, i, j);
        return;
      }
      j := j + 1;
    }
    
    PreserveDuplicateInvariant(lst, i);
    i := i + 1;
  }
  
  // At this point, we've checked all pairs and found no duplicates
  assert forall k, l :: 0 <= k < l < |lst| ==> lst[k] != lst[l];
}
// </vc-code>
