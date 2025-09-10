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
  requires !ImpossibleConditions(a, b, f, k)
  ensures result >= 0 ==> (b >= f && b >= a - f && b >= 2 * a - f)
{
  if result >= 0 {
    assert b >= f;
    assert b >= a - f;
    assert b >= 2 * a - f;
  }
}

lemma FeasibilityLemma(a: int, b: int, f: int, k: int)
  requires ValidInput(a, b, f, k)
  ensures FeasibilityConditions(a, b, f, k) <==> !ImpossibleConditions(a, b, f, k)
{
}

lemma FuelCheckLemma(a: int, b: int, f: int, k: int)
  requires ValidInput(a, b, f, k)
  requires !ImpossibleConditions(a, b, f, k)
  ensures b >= f && b >= a - f && (k <= 1 || b >= 2 * a - f)
{
  if k > 1 {
    assert b >= 2 * a - f;
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
  if ImpossibleConditions(a, b, f, k) {
    result := -1;
  } else if k == 1 {
    if b >= a {
      result := 0;
    } else {
      result := 1;
    }
    assert result >= 0 ==> ((b >= a && result == 0) || (b < a && b >= f && result == 1));
  } else {
    var remaining_fuel := b;
    var refills := 0;
    var i := 1;
    
    while i < k
      invariant 1 <= i <= k
      invariant refills >= 0 && refills <= i
      invariant remaining_fuel >= 0
      invariant remaining_fuel <= b
    {
      if i % 2 == 1 {
        remaining_fuel := remaining_fuel - (a - f);
        if remaining_fuel < 0 {
          refills := refills + 1;
          remaining_fuel := b - (a - f);
          assert remaining_fuel >= 0;
        }
      } else {
        remaining_fuel := remaining_fuel - f;
        if remaining_fuel < 0 {
          refills := refills + 1;
          remaining_fuel := b - f;
          assert remaining_fuel >= 0;
        }
      }
      i := i + 1;
    }
    
    if k % 2 == 1 {
      if remaining_fuel >= a - f {
        result := refills;
      } else {
        result := refills + 1;
      }
    } else {
      if remaining_fuel >= f {
        result := refills;
      } else {
        result := refills + 1;
      }
    }
    
    assert result <= k;
    assert result >= 0 ==> FeasibilityConditions(a, b, f, k);
  }
}
// </vc-code>

