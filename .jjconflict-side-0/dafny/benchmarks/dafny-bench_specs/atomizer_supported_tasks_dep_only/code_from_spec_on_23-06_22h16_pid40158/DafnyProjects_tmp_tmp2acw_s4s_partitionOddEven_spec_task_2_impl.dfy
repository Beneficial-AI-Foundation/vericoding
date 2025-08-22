//IMPL partitionOddEven
// Rearranges the elements in an array 'a' of natural numbers,
// so that all odd numbers appear before all even numbers.
method partitionOddEven(a: array<nat>) 
  modifies a
  ensures multiset(a[..]) == multiset(old(a[..]))
  ensures ! exists i, j :: 0 <= i < j < a.Length && even(a[i]) && odd(a[j])  
{
  if a.Length <= 1 {
    return;
  }
  
  var left := 0;
  var right := a.Length - 1;
  
  while left < right
    invariant 0 <= left <= right + 1 <= a.Length
    invariant multiset(a[..]) == multiset(old(a[..]))
    invariant forall k :: 0 <= k < left ==> odd(a[k])
    invariant forall k :: right < k < a.Length ==> even(a[k])
    /* code modified by LLM (iteration 4): Simplified invariant to avoid complex nested quantifiers */
    invariant forall i, j :: 0 <= i < left && right < j < a.Length ==> !(even(a[i]) && odd(a[j]))
  {
    if odd(a[left]) {
      left := left + 1;
    } else if even(a[right]) {
      right := right - 1;
    } else {
      // a[left] is even and a[right] is odd, so swap them
      var temp := a[left];
      a[left] := a[right];
      a[right] := temp;
      left := left + 1;
      right := right - 1;
    }
  }
  
  /* code modified by LLM (iteration 4): Simplified postcondition proof with helper lemma */
  partitionProofHelper(a, left);
}

/* code modified by LLM (iteration 4): Added helper lemma to prove postcondition */
lemma partitionProofHelper(a: array<nat>, left: int)
  requires 0 <= left <= a.Length
  requires forall k :: 0 <= k < left ==> odd(a[k])
  requires forall k :: left <= k < a.Length ==> even(a[k])
  ensures ! exists i, j :: 0 <= i < j < a.Length && even(a[i]) && odd(a[j])
{
  if exists i, j :: 0 <= i < j < a.Length && even(a[i]) && odd(a[j]) {
    var i, j :| 0 <= i < j < a.Length && even(a[i]) && odd(a[j]);
    if i < left {
      assert odd(a[i]);
      assert false;
    } else {
      assert j >= left;
      assert even(a[j]);
      assert false;
    }
  }
}

//ATOM 
predicate  odd(n: nat) { n % 2 == 1 }

//ATOM 
predicate  even(n: nat) { n % 2 == 0 }

//IMPL testPartitionOddEven
method testPartitionOddEven() {
  var a := new nat[5];
  a[0] := 2; a[1] := 3; a[2] := 4; a[3] := 1; a[4] := 6;
  /* code modified by LLM (iteration 4): Store original values for verification */
  ghost var originalMultiset := multiset(a[..]);
  partitionOddEven(a);
  /* code modified by LLM (iteration 4): Verify both postconditions of partitionOddEven */
  assert multiset(a[..]) == originalMultiset;
  assert ! exists i, j :: 0 <= i < j < a.Length && even(a[i]) && odd(a[j]);
  assert multiset(a[..]) == multiset([2, 3, 4, 1, 6]);
}