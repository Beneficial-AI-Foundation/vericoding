predicate ValidInput(p: int) {
    2 <= p < 2000
}

function CountPrimitiveRoots(p: int): int
    requires ValidInput(p)
{
    if p == 2 then 1
    else |set i | 1 <= i < p-1 && (forall j :: 2 <= j <= i ==> !((p-1) % j == 0 && i % j == 0))|
}

// <vc-helpers>
// No helper functions required for this implementation.
// </vc-helpers>

// <vc-spec>
method solve(p: int) returns (result: int)
    requires ValidInput(p)
    ensures result >= 0
    ensures result == CountPrimitiveRoots(p)
// </vc-spec>
// <vc-code>
{
  if p == 2 {
    return 1;
  }
  var count := 0;
  var i := 1;
  // iterate i over 1 .. p-2
  while i <= p-2
    invariant 1 <= i <= p-1
    invariant count == |set x | 1 <= x < i && (forall j :: 2 <= j <= x ==> !((p-1) % j == 0 && x % j == 0))|
    decreases p - i
  {
    var ok := true;
    var j := 2;
    // check if there exists a common divisor j in 2..i
    while j <= i
      invariant 2 <= j <= i+1
      invariant ok == (forall k :: 2 <= k < j ==> !((p-1) % k == 0 && i % k == 0))
      decreases i - j + 1
    {
      if (p-1) % j == 0 && i % j == 0 {
        ok := false;
      }
      j := j + 1;
    }
    if ok {
      count := count + 1;
    }
    i := i + 1;
  }
  return count;
}
// </vc-code>

