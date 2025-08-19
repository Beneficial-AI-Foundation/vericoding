//IMPL intDivImpl
method intDivImpl(n:int, d:int) returns (q:int, r:int)
requires n >= d && n >= 0 && d > 0
ensures (d*q)+r == n && 0 <= q <= n/2 && 0 <= r < d
{
    var standardQ := n / d;
    var standardR := n % d;
    
    if standardQ <= n / 2 {
        q := standardQ;
        r := standardR;
    } else {
        /* code modified by LLM (iteration 4): Search for valid q starting from 0 up to n/2 */
        q := 0;
        r := n;
        
        /* code modified by LLM (iteration 4): Find the largest valid q <= n/2 such that r < d */
        var candidate_q := 0;
        while candidate_q <= n / 2
            invariant candidate_q >= 0
            invariant q >= 0 && q <= n / 2
            invariant r == n - d * q
            invariant (d * q) + r == n
            decreases n / 2 - candidate_q
        {
            var candidate_r := n - d * candidate_q;
            if candidate_r >= 0 && candidate_r < d {
                q := candidate_q;
                r := candidate_r;
            }
            candidate_q := candidate_q + 1;
        }
        
        /* code modified by LLM (iteration 4): Assert that we found a valid solution */
        assert q >= 0 && q <= n / 2;
        assert r == n - d * q;
        assert (d * q) + r == n;
        assert r < d;
    }
}