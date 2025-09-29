

// <vc-helpers>
lemma SetCardinalityDecrease<T>(s: set<T>, x: T)
  requires x in s
  ensures |s - {x}| == |s| - 1
{
}

lemma FilteredSetPartition(numbers: set<int>, threshold: int, x: int)
  requires x in numbers
  ensures x < threshold ==> 
    |set i | i in (numbers - {x}) && i < threshold| == 
    |set i | i in numbers && i < threshold| - 1
  ensures x >= threshold ==> 
    |set i | i in (numbers - {x}) && i < threshold| == 
    |set i | i in numbers && i < threshold|
{
  var filtered := set i | i in numbers && i < threshold;
  var filteredWithoutX := set i | i in (numbers - {x}) && i < threshold;
  
  if x < threshold {
    assert filtered == filteredWithoutX + {x};
    assert x in filtered;
    assert filteredWithoutX == filtered - {x};
    SetCardinalityDecrease(filtered, x);
  } else {
    assert x !in filtered;
    assert filtered == filteredWithoutX;
  }
}
// </vc-helpers>

// <vc-spec>
method CountLessThan(numbers: set<int>, threshold: int) returns (count: int)
  ensures count == |set i | i in numbers && i < threshold|
// </vc-spec>
// <vc-code>
{
  count := 0;
  var remaining := numbers;
  
  while remaining != {}
    decreases remaining
    invariant count == |set i | i in (numbers - remaining) && i < threshold|
  {
    var x :| x in remaining;
    if x < threshold {
      count := count + 1;
    }
    
    FilteredSetPartition(numbers - (remaining - {x}), threshold, x);
    assert numbers - (remaining - {x}) == numbers - remaining + {x};
    
    remaining := remaining - {x};
  }
  
  assert remaining == {};
  assert numbers - remaining == numbers;
}
// </vc-code>

