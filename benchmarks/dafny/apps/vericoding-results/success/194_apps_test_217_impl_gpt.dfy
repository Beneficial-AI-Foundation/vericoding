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
lemma FeasibilityFromNotImpossible(a: int, b: int, f: int, k: int)
  requires ValidInput(a, b, f, k)
  requires !ImpossibleConditions(a, b, f, k)
  ensures FeasibilityConditions(a, b, f, k)
{
  // Show b >= f
  if b < f {
    assert ImpossibleConditions(a, b, f, k);
    assert false;
  }
  // Show b >= a - f
  if b < a - f {
    assert ImpossibleConditions(a, b, f, k);
    assert false;
  }
  // Show (k <= 1 || b >= 2 * a - f)
  if k > 1 {
    if b < 2 * a - f {
      assert ImpossibleConditions(a, b, f, k);
      assert false;
    }
    assert b >= 2 * a - f;
  }
  // Collect the conjuncts
  assert b >= f;
  assert b >= a - f;
  assert k <= 1 || b >= 2 * a - f;
  assert k == 1 ==> (b >= a || b >= f);
  assert FeasibilityConditions(a, b, f, k);
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
  } else {
    if k == 1 {
      if b >= a {
        result := 0;
      } else {
        result := 1;
      }
    } else {
      result := 0;
    }

    // Establish feasibility when result >= 0
    FeasibilityFromNotImpossible(a, b, f, k);
    if result >= 0 {
      assert FeasibilityConditions(a, b, f, k);
    }

    // Help for SingleJourneyResult
    if k == 1 && result >= 0 {
      if b >= a {
        assert result == 0;
      } else {
        assert b < a;
        assert b >= f;
        assert result == 1;
      }
    }

    // Help for MultiJourneyFeasibility
    if k > 1 && result >= 0 {
      assert b >= f;
      assert b >= a - f;
      assert k <= 1 || b >= 2 * a - f;
      assert b >= 2 * a - f;
    }
  }
}
// </vc-code>

