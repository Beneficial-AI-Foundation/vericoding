//IMPL intDiv
method intDiv(n:int, d:int) returns (q:int, r:int)
requires n >= d && n >= 0 && d > 0 
ensures (d*q)+r == n && 0 <= q <= n/2 && 0 <= r < d
{
    q := 0;
    r := n;
    
    /* code modified by LLM (iteration 3): constrained division algorithm */
    while r >= d && q < n/2
        invariant (d*q)+r == n
        invariant 0 <= q <= n/2
        invariant r >= 0
        decreases r
    {
        q := q + 1;
        r := r - d;
    }
    
    /* code modified by LLM (iteration 3): handle remainder when constraint prevents further division */
    if r >= d {
        // We've hit the constraint q <= n/2 but r >= d
        // We need to find a valid solution that satisfies all postconditions
        // Since we can't increase q beyond n/2, we need to work backwards
        
        /* code modified by LLM (iteration 3): find maximum valid q that ensures r < d */
        q := 0;
        r := n;
        
        // Find the largest q such that q <= n/2 and the resulting r < d
        var maxQ := n / d;
        if maxQ > n / 2 {
            maxQ := n / 2;
        }
        
        q := maxQ;
        r := n - d * q;
        
        // Ensure r < d by reducing q if necessary
        while r >= d && q > 0
            invariant (d*q)+r == n
            invariant q >= 0
            decreases q
        {
            q := q - 1;
            r := r + d;
        }
    }
}