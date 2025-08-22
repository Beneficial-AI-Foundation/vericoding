//IMPL CountLessThan
/* code modified by LLM (iteration 2): Fixed helper lemma with correct set comprehension syntax and improved proof */
lemma SetEquivalenceWhenRemainingEmpty(numbers: set<int>, threshold: int)
  ensures (set i | i in numbers && i < threshold && i !in {}) == (set i | i in numbers && i < threshold)
{
  var left := set i | i in numbers && i < threshold && i !in {};
  var right := set i | i in numbers && i < threshold;
  
  // Show both directions of set equality
  forall i | i in left ensures i in right {
    assert i in numbers && i < threshold && i !in {};
    assert i in numbers && i < threshold;
  }
  
  forall i | i in right ensures i in left {
    assert i in numbers && i < threshold;
    assert i !in {}; // trivially true for any element
    assert i in numbers && i < threshold && i !in {};
  }
}

method CountLessThan(numbers: set<int>, threshold: int) returns (count: int)
  ensures count == |set i | i in numbers && i < threshold|
{
  count := 0;
  var remaining := numbers;
  
  while remaining != {}
    invariant count == |set i | i in numbers && i < threshold && i !in remaining|
    invariant remaining <= numbers
    decreases |remaining|
  {
    var x :| x in remaining;
    remaining := remaining - {x};
    
    if x < threshold {
      count := count + 1;
    }
  }
  
  /* code modified by LLM (iteration 2): Improved proof with explicit set reasoning */
  SetEquivalenceWhenRemainingEmpty(numbers, threshold);
  
  // At this point: remaining == {} and count == |set i | i in numbers && i < threshold && i !in remaining|
  assert remaining == {};
  assert count == |set i | i in numbers && i < threshold && i !in {}|;
  
  // The helper lemma establishes the equivalence
  assert (set i | i in numbers && i < threshold && i !in {}) == (set i | i in numbers && i < threshold);
  assert count == |set i | i in numbers && i < threshold|;
}