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
lemma SingleJourneyLemma(a: int, b: int, f: int, k: int, result: int)
  requires ValidInput(a, b, f, k)
  requires k == 1
  ensures result >= 0 ==> ((b >= a && result == 0) || (b < a && b >= f && result == 1))
{
}

lemma MultiJourneyLemma(a: int, b: int, f: int, k: int, result: int)
  requires ValidInput(a, b, f, k)
  requires k > 1
  ensures result >= 0 ==> (b >= f && b >= a - f && b >= 2 * a - f)
{
}

lemma FeasibilityLemma(a: int, b: int, f: int, k: int)
  requires ValidInput(a, b, f, k)
  ensures FeasibilityConditions(a, b, f, k) <==> !ImpossibleConditions(a, b, f, k)
{
  // This lemma establishes the equivalence between feasibility and not impossible
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
  if b < f || b < a - f || (k > 1 && b < 2 * a - f) || (k == 1 && b < a && b < f) {
    result := -1;
  } else if k == 1 {
    if b >= a {
      result := 0;
    } else if b >= f {
      result := 1;
    } else {
      result := -1;
    }
  } else {
    // For k > 1 journeys, we need to calculate the number of refills
    var remaining_fuel := b - f;
    var refills := 0;
    var i := 1;
    
    while i < k && remaining_fuel >= 0
      invariant 0 <= i <= k
      invariant refills >= 0
    {
      if i % 2 == 1 {
        // Going from start to destination (right direction)
        if remaining_fuel < a - f {
          refills := refills + 1;
          remaining_fuel := b - (a - f);
        } else {
          remaining_fuel := remaining_fuel - (a - f);
        }
      } else {
        // Going from destination to start (left direction)
        if remaining_fuel < f {
          refills := refills + 1;
          remaining_fuel := b - f;
        } else {
          remaining_fuel := remaining_fuel - f;
        }
      }
      i := i + 1;
    }
    
    // Check if we can complete the last journey
    if k % 2 == 1 {
      // Last journey is from start to destination
      if remaining_fuel >= a - f {
        result := refills;
      } else if remaining_fuel + b >= a - f {
        result := refills + 1;
      } else {
        result := -1;
      }
    } else {
      // Last journey is from destination to start
      if remaining_fuel >= f {
        result := refills;
      } else if remaining_fuel + b >= f {
        result := refills + 1;
      } else {
        result := -1;
      }
    }
  }
}
// </vc-code>

