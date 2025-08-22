//IMPL CountLessThan
method CountLessThan(numbers: set<int>, threshold: int) returns (count: int)
  ensures count == |set i | i in numbers && i < threshold|
{
  count := 0;
  var remaining := numbers;
  
  while remaining != {}
    invariant count == |set i | i in (numbers - remaining) && i < threshold|
    invariant remaining <= numbers
    /* code modified by LLM (iteration 4): Added invariant to help Dafny track the relationship between sets */
    invariant numbers - remaining == numbers - remaining
    decreases |remaining|
  {
    var x :| x in remaining;
    remaining := remaining - {x};
    
    if x < threshold {
      count := count + 1;
    }
  }
  
  /* code modified by LLM (iteration 4): Added step-by-step proof that sets are equivalent */
  assert remaining == {};
  assert numbers - {} == numbers;
  assert numbers - remaining == numbers;
  assert count == |set i | i in (numbers - remaining) && i < threshold|;
  assert (set i | i in (numbers - remaining) && i < threshold) == (set i | i in numbers && i < threshold);
}