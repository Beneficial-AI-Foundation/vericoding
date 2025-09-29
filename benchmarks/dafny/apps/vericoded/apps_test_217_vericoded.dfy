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
// Helper lemmas for verification
lemma ImpossibleImpliesNotFeasible(a: int, b: int, f: int, k: int)
  requires ValidInput(a, b, f, k)
  ensures ImpossibleConditions(a, b, f, k) ==> !FeasibilityConditions(a, b, f, k)
{
  if ImpossibleConditions(a, b, f, k) {
    if b < f || b < a - f {
      assert !FeasibilityConditions(a, b, f, k);
    } else if k > 1 && b < 2 * a - f {
      assert !FeasibilityConditions(a, b, f, k);
    } else if k == 1 && b < a && b < f {
      assert !FeasibilityConditions(a, b, f, k);
    }
  }
}

lemma FeasibleImpliesNotImpossible(a: int, b: int, f: int, k: int)
  requires ValidInput(a, b, f, k)
  ensures FeasibilityConditions(a, b, f, k) ==> !ImpossibleConditions(a, b, f, k)
{
  if FeasibilityConditions(a, b, f, k) {
    assert b >= f && b >= a - f;
    if k > 1 {
      assert b >= 2 * a - f;
    }
    if k == 1 {
      assert b >= a || b >= f;
    }
    assert !ImpossibleConditions(a, b, f, k);
  }
}
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
  // Check impossible conditions first
  if b < f || b < a - f {
    return -1;
  }
  
  if k == 1 {
    // Single refueling case
    if b >= a {
      // Can reach office without refueling
      return 0;
    } else if b >= f {
      // Can reach gas station and then office with one refueling
      return 1;
    } else {
      // Cannot reach gas station
      return -1;
    }
  } else {
    // Multiple refuelings allowed (k > 1)
    if b < 2 * a - f {
      // Cannot complete a round trip even with refueling
      return -1;
    }
    
    // Can complete round trips
    // We need at most 2 refuelings per round trip
    // (one at gas station going to office, one coming back)
    var refuels := 0;
    var fuel := b;
    
    // First trip to office
    if fuel < a {
      // Need to refuel at gas station
      refuels := refuels + 1;
      fuel := b;  // Tank is full after refueling
    }
    fuel := fuel - a;  // Consume fuel to reach office
    
    // Return trip
    if fuel < a {
      // Need to refuel at gas station on way back
      if fuel < a - f {
        // Cannot reach gas station on way back
        return -1;
      }
      refuels := refuels + 1;
      fuel := b;  // Tank is full after refueling
    }
    
    // Verify we don't exceed k
    if refuels > k {
      return -1;
    }
    
    return refuels;
  }
}
// </vc-code>

