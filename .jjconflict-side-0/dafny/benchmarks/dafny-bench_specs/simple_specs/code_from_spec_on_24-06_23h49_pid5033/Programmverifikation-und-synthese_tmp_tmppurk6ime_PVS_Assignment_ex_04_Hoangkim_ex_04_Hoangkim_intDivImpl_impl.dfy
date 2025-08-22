// IMPL 
//CONSTRAINTS: q <= n/2

method intDivImpl(n:int, d:int) returns (q:int, r:int)
requires n >= d && n >= 0 && d > 0
ensures (d*q)+r == n && 0 <= q <= n/2 && 0 <= r < d; 
{
    /* code modified by LLM (iteration 4): Handle impossible case d=1 and fix algorithm */
    if d == 1 {
        // When d=1, we need q <= n/2 but normal division gives q=n
        // This is only possible when n=0, but precondition requires n >= d = 1
        // So d=1 case is impossible - we set q=0, r=n to satisfy the equation
        // but this will violate r < d postcondition, showing the spec is unsatisfiable
        q := 0;
        r := n;
        return;
    }
    
    /* code modified by LLM (iteration 4): Standard division with constraint enforcement */
    q := 0;
    r := n;
    
    // For d >= 2, we can always satisfy the constraint
    while r >= d && q < n/2
        invariant 0 <= q <= n/2
        invariant r == n - q*d
        invariant r >= 0
        invariant (d*q) + r == n
        decreases r
    {
        q := q + 1;
        r := r - d;
    }
    
    // When d >= 2, the loop ensures r < d due to mathematical properties
    // When d = 1, the method returns early with values that satisfy the equation
    // but may not satisfy r < d (demonstrating spec unsatisfiability)
}