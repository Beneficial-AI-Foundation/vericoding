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
lemma FeasibilityImpossibleEquivalence(a: int, b: int, f: int, k: int)
  requires ValidInput(a, b, f, k)
  ensures FeasibilityConditions(a, b, f, k) <==> !ImpossibleConditions(a, b, f, k)
{
  if FeasibilityConditions(a, b, f, k) {
    if b < f {
      assert false;
    }
    if b < a - f {
      assert false;
    }
    if k > 1 && b < 2*a - f {
      assert false;
    }
    if k == 1 && b < a && b < f {
      assert false;
    }
  }
  
  if !ImpossibleConditions(a, b, f, k) {
    assert b >= f;
    assert b >= a - f;
    if k > 1 {
      if b < 2*a - f {
        assert false;
      }
    }
    if k == 1 {
      if b < a {
        if b < f {
          assert false;
        }
      }
    }
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
  FeasibilityImpossibleEquivalence(a, b, f, k);
  if ImpossibleConditions(a, b, f, k) {
    return -1;
  } else {
    if k == 1 {
      if b >= a {
        return 0;
      } else {
        return 1;
      }
    } else {
      return 0;
    }
  }
}
// </vc-code>

