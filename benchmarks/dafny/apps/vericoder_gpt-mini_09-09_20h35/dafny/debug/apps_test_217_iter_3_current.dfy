predicate ValidInput(a: int, b: int, f: int, k: int) {
  a > 0 && b > 0 && f > 0 && k > 0 && f < a
}

predicate ImpossibleConditions(a: int, b: int, f: int, k: int) {
  b < f ||                                    
  b < a - f ||                               
  (k > 1 && b < 2 * a - f) ||               
  (k == 1 && b < a && b < f)                
}

predicate FeasibilityConditions(a: int, b: int, f: int, k: int) {
  b >= f &&                                  
  b >= a - f &&                             
  (k <= 1 || b >= 2 * a - f) &&            
  (k == 1 ==> (b >= a || b >= f))          
}

predicate SingleJourneyResult(a: int, b: int, f: int, k: int, result: int) {
  k == 1 && result >= 0 ==> (
    (b >= a && result == 0) ||                
    (b < a && b >= f && result == 1)          
  )
}

predicate MultiJourneyFeasibility(a: int, b: int, f: int, k: int, result: int) {
  k > 1 && result >= 0 ==> (
    b >= f && b >= a - f && b >= 2 * a - f    
  )
}

// <vc-helpers>
// No helper lemmas required for this implementation.
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, f: int, k: int) returns (result: int)
  requires ValidInput(a, b, f, k)
  ensures result >= -1
  ensures result == -1 <==> ImpossibleConditions(a, b, f, k)
  ensures result >= 0 ==> result <= k
  ensures result >= 0 ==> FeasibilityConditions(a, b, f, k)
  ensures SingleJourneyResult(a, b, f, k, result)
  ensures MultiJourneyFeasibility(a, b, f, k, result)
// </vc-spec>
// <vc-code>
{
  var fuel := b;
  var side := 0; // 0 = left, 1 = right
  var cnt := 0;
  if k == 1 {
    if b < f || b < a - f {
      result := -1;
      return;
    }
    if b >= a {
      // feasible, so impossible conditions do not hold
      assert !ImpossibleConditions(a, b, f, k);
      result := 0;
      return;
    }
    // b < a but b >= f and b >= a - f (checked), so one refuel at station suffices
    assert !ImpossibleConditions(a, b, f, k);
    result := 1;
    return;
  } else {
    if b < f || b < a - f || b < 2 * a - f {
      result := -1;
      return;
    }
    var i := 0;
    while i < k
      invariant 0 <= i <= k
      invariant 0 <= cnt <= k
      invariant cnt <= i
      invariant fuel >= 0
      invariant side == 0 || side == 1
    {
      var stationDist := if side == 0 then f else a - f;
      if fuel >= a {
        fuel := fuel - a;
      } else {
        // go to station (stationDist is reachable due to initial checks and loop behavior)
        fuel := fuel - stationDist;
        cnt := cnt + 1;
        // refill
        fuel := b;
        var rem := a - stationDist;
        // rem is <= b due to initial checks
        fuel := fuel - rem;
      }
      side := 1 - side;
      i := i + 1;
    }
    // initial checks ensured ImpossibleConditions does not hold in this branch
    assert !ImpossibleConditions(a, b, f, k);
    result := cnt;
    return;
  }
}
// </vc-code>

