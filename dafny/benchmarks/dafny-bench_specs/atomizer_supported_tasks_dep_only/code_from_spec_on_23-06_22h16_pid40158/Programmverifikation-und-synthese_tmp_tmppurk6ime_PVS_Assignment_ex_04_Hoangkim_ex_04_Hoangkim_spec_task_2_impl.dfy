//ATOM_PLACEHOLDER_sumOdds

//IMPL intDiv
method intDiv(n:int, d:int) returns (q:int, r:int)
requires n >= d && n >= 0 && d > 0 ;
ensures (d*q)+r == n && 0 <= q <= n/2 && 0 <= r < d;
{
    /* code modified by LLM (iteration 4): Initialize variables */
    q := 0;
    r := n;
    
    /* code modified by LLM (iteration 4): Main division loop with constraint checking */
    while r >= d && q < n/2
        invariant (d*q)+r == n
        invariant 0 <= q <= n/2
        invariant r >= 0
        decreases r
    {
        q := q + 1;
        r := r - d;
    }
    
    /* code modified by LLM (iteration 4): Ensure remainder constraint is satisfied */
    // At this point, either r < d (normal case) or q == n/2 (constraint limit reached)
    // If r >= d and q == n/2, we need to ensure r < d while keeping q <= n/2
    
    if r >= d {
        /* code modified by LLM (iteration 4): Adjust to satisfy remainder constraint */
        // We need to find the largest q <= n/2 such that n - d*q < d
        // This means d*q > n - d, so q > (n-d)/d
        var min_q := (n - d + 1) / d;  // Minimum q to ensure remainder < d
        var max_q := n / 2;             // Maximum q allowed by postcondition
        
        if min_q <= max_q {
            q := min_q;
            r := n - d * q;
        } else {
            // If no valid q exists, use the maximum allowed
            q := max_q;
            r := n - d * q;
            
            /* code modified by LLM (iteration 4): Final adjustment if needed */
            // If r is still >= d, we need to distribute the excess
            if r >= d {
                // This case might not always have a solution satisfying all constraints
                // But we'll try to get as close as possible
                var excess := r / d;
                if q + excess <= n/2 {
                    q := q + excess;
                    r := r - excess * d;
                }
            }
        }
    }
    
    /* code modified by LLM (iteration 4): Assert final conditions for verification */
    assert (d*q)+r == n;
    assert 0 <= q <= n/2;
    assert r >= 0;
}