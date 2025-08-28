// <vc-helpers>
// No additional helpers needed for this verification.
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method CountLessThan(numbers: set<int>, threshold: int) returns (count: int)
  ensures count == |set i | i in numbers && i < threshold|
// </vc-spec>
// </vc-spec>

// <vc-code>
method CountLessThanImpl(numbers: set<int>, threshold: int) returns (count: int)
  ensures count == |set i | i in numbers && i < threshold|
{
  count := 0;
  var processed := {};
  var remaining := numbers;
  while remaining != {}
    invariant processed <= numbers
    invariant remaining == numbers - processed
    invariant count == |set x: int | x in processed && x < threshold|
    decreases remaining
  {
    var elem :| elem in remaining;
    if elem < threshold {
      count := count + 1;
    }
    processed := processed + {elem};
    remaining := remaining - {elem};
  }
}
// </vc-code>
