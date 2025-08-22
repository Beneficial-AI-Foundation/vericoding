//IMPL intDivImpl
method intDivImpl(n:int, d:int) returns (q:int, r:int)
requires n >= d && n >= 0 && d > 0;
ensures (d*q)+r == n && 0 <= q <= n/2 && 0 <= r < d; 
{
    /* code modified by LLM (iteration 4): Initialize with values that satisfy the equation */
    q := 0;
    r := n;
    
    /* code modified by LLM (iteration 4): Search for largest valid q that satisfies all constraints */
    var candidate_q := 0;
    while candidate_q <= n / 2
        invariant 0 <= candidate_q <= n / 2 + 1
        invariant (d * q) + r == n
        invariant 0 <= q <= n / 2
        invariant 0 <= r
        decreases n / 2 + 1 - candidate_q
    {
        var candidate_r := n - d * candidate_q;
        if candidate_r >= 0 && candidate_r < d {
            q := candidate_q;
            r := candidate_r;
        }
        candidate_q := candidate_q + 1;
    }
    
    /* code modified by LLM (iteration 4): Assert that we found a valid solution */
    assert (d * q) + r == n;
    assert 0 <= q <= n / 2;
    
    /* code modified by LLM (iteration 4): Ensure r < d constraint is met */
    if r >= d {
        // If no valid solution was found, this specification is unsatisfiable
        // But we need to satisfy the postcondition, so we'll use the minimal valid assignment
        q := 0;
        r := n;
        // This may still not satisfy r < d, indicating the specification may be unsatisfiable
        // for certain inputs, but we maintain the equation
    }
}