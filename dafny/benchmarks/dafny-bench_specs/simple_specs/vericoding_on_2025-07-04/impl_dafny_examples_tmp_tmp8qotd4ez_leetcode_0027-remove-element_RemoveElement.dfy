//IMPL
method RemoveElement(nums: array<int>, val: int) returns (newLength: int)
  modifies nums
  ensures 0 <= newLength <= nums.Length
  ensures forall x :: x in nums[..newLength] ==> x != val
  ensures multiset(nums[..newLength]) == multiset(old(nums[..])) - multiset(seq(nums.Length, i => val))
{
  /* code modified by LLM (iteration 4): ghost variable to track original array */
  ghost var original := nums[..];
  
  newLength := 0;
  var i := 0;
  
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    invariant 0 <= newLength <= i
    invariant forall x :: x in nums[..newLength] ==> x != val
    /* code modified by LLM (iteration 4): track that result contains non-val elements from processed portion */
    invariant multiset(nums[..newLength]) <= multiset(original[..i])
    invariant forall x :: x in nums[..newLength] ==> x in original[..i] && x != val
    /* code modified by LLM (iteration 4): count invariant - newLength equals non-val elements in processed portion */
    invariant newLength == |original[..i]| - |multiset(original[..i]) * multiset{val}|
  {
    if nums[i] != val {
      nums[newLength] := nums[i];
      newLength := newLength + 1;
    }
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 4): establish postcondition using multiset intersection properties */
  assert original[..i] == original;
  
  /* code modified by LLM (iteration 4): key insight - the result is original minus all val occurrences */
  ghost var valsInOriginal := multiset(original) * multiset{val};
  assert multiset(nums[..newLength]) == multiset(original) - valsInOriginal;
  
  /* code modified by LLM (iteration 4): show equivalence with postcondition multiset */
  ghost var postConditionRemoval := multiset(seq(nums.Length, i => val));
  
  /* code modified by LLM (iteration 4): lemma application - intersection with singleton equals repeated removal */
  assert valsInOriginal <= postConditionRemoval;
  assert multiset(original) - valsInOriginal == multiset(original) - (valsInOriginal + (postConditionRemoval - valsInOriginal));
  assert multiset(original) - postConditionRemoval == multiset(original) - valsInOriginal;
}