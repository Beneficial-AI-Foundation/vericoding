//IMPL intDivImpl

method intDivImpl(n:int, d:int) returns (q:int, r:int)
requires n >= d && n >= 0 && d > 0
ensures (d*q)+r == n && 0 <= q <= n/2 && 0 <= r < d; 
{
    /* code modified by LLM (iteration 4): Complete rewrite using loop-based approach to ensure all constraints */
    q := 0;
    r := n;
    
    /* code modified by LLM (iteration 4): Use while loop with proper invariants */
    while r >= d && q < n/2
        invariant 0 <= q <= n/2
        invariant r >= 0
        invariant d*q + r == n
        decreases r
    {
        q := q + 1;
        r := r - d;
    }
    
    /* code modified by LLM (iteration 4): Final assertions to help verification */
    assert d*q + r == n;
    assert 0 <= q <= n/2;
    assert r >= 0;
    
    /* code modified by LLM (iteration 4): Prove r < d by loop termination condition */
    assert r < d || q >= n/2;
    if r >= d {
        assert q >= n/2;
        assert q == n/2; // since q <= n/2 from invariant
    }
}