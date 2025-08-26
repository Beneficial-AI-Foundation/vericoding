function C(n: nat): nat 
    decreases n
{
    if n == 0 then 1 else (4 * n - 2) * C(n-1) / (n + 1) 
}

// <vc-helpers>
lemma CRecursiveProperty(i: nat)
    requires i > 0
    ensures C(i) == (4 * i - 2) * C(i-1) / (i + 1)
{
    // This follows directly from the definition of C
}

lemma CDivisibilityProperty(i: nat)
    requires i > 0
    ensures (4 * i - 2) * C(i-1) % (i + 1) == 0
{
    // We prove this by induction on i
    if i == 1 {
        // Base case: i = 1
        // (4*1-2) * C(0) = 2 * 1 = 2
        // 2 % 2 = 0
        assert C(0) == 1;
        assert (4 * 1 - 2) * C(0) == 2;
        assert 2 % 2 == 0;
    } else {
        // Inductive step: assume it holds for i-1, prove for i
        // The key insight is that C(i) being a natural number
        // means the division must be exact
        CDivisibilityProperty(i-1);
        
        // Since C(i) is well-defined as a nat, the division must be exact
        var numerator := (4 * i - 2) * C(i-1);
        var denominator := i + 1;
        var result := C(i);
        
        // From the definition, we know C(i) = numerator / denominator
        assert result == numerator / denominator;
        
        // Since the result is a natural number, the division must be exact
        assert numerator == result * denominator;
        assert numerator % denominator == 0;
    }
}
// </vc-helpers>

// <vc-spec>
method calcC(n: nat) returns (res: nat)
    ensures res == C(n)
// </vc-spec>
// <vc-code>
{
  res := 1;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant res == C(i)
  {
    i := i + 1;
    
    // Add assertion to help verification
    assert i > 0;
    assert res == C(i-1);
    
    // Use the lemma to establish the recursive property
    CRecursiveProperty(i);
    CDivisibilityProperty(i);
    
    // Now perform the calculation
    res := (4 * i - 2) * res / (i + 1);
    
    // Assert the postcondition
    assert res == C(i);
  }
}
// </vc-code>