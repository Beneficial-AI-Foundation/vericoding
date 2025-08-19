//IMPL
method SmallestMissingNumber(s: seq<int>) returns (v: int)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  requires forall i :: 0 <= i < |s| ==> s[i] >= 0
  ensures 0 <= v
  ensures v !in s
  ensures forall k :: 0 <= k < v ==> k in s
{
  var i := 0;
  while i < |s| && s[i] == i
    invariant 0 <= i <= |s|
    /* code modified by LLM (iteration 4): fixed loop invariant to properly establish that all elements 0..i-1 are in s */
    invariant forall k :: 0 <= k < i ==> k in s
    /* code modified by LLM (iteration 4): added invariant to maintain that s[j] == j for all j < i */
    invariant forall j :: 0 <= j < i ==> s[j] == j
  {
    i := i + 1;
  }
  v := i;
  
  /* code modified by LLM (iteration 4): restructured proof to clearly establish all postconditions */
  
  // First, establish that v >= 0 (trivial since i >= 0)
  assert v >= 0;
  
  // Prove that forall k :: 0 <= k < v ==> k in s
  /* code modified by LLM (iteration 4): explicit proof that all numbers less than v are in s */
  assert forall k :: 0 <= k < v ==> k in s by {
    forall k | 0 <= k < v
      ensures k in s
    {
      assert k < i; // since v == i
      assert k in s; // from loop invariant
    }
  }
  
  // Prove that v !in s
  if i < |s| {
    /* code modified by LLM (iteration 4): clearer proof when loop terminated early */
    // Loop terminated because s[i] != i, and we know s[i] >= 0
    assert s[i] != i;
    assert s[i] >= 0; // from precondition
    
    // Since s[i] != i and s[i] >= 0, we must have s[i] > i (because s[i] can't be < i due to sortedness)
    assert s[i] > i by {
      if s[i] < i {
        // This would contradict sortedness and our loop invariant
        assert forall j :: 0 <= j < i ==> s[j] == j;
        assert s[i-1] == i-1; // if i > 0
        assert s[i-1] <= s[i]; // sortedness
        assert i-1 <= s[i] < i; // contradiction
        assert false;
      }
    }
    
    /* code modified by LLM (iteration 4): prove v not in s by case analysis */
    assert v !in s by {
      forall j | 0 <= j < |s|
        ensures s[j] != v
      {
        if j < i {
          assert s[j] == j < i;
          assert s[j] < v;
        } else {
          assert j >= i;
          assert s[j] >= s[i] > i; // by sortedness
          assert s[j] > v;
        }
      }
    }
  } else {
    /* code modified by LLM (iteration 4): clearer proof when we've gone through entire sequence */
    // i == |s|, so we've seen all elements and they were all 0, 1, ..., |s|-1
    assert i == |s|;
    assert v == |s|;
    
    /* code modified by LLM (iteration 4): prove v not in s when v equals sequence length */
    assert v !in s by {
      forall j | 0 <= j < |s|
        ensures s[j] != v
      {
        assert s[j] == j < |s|;
        assert s[j] < v;
      }
    }
  }
}