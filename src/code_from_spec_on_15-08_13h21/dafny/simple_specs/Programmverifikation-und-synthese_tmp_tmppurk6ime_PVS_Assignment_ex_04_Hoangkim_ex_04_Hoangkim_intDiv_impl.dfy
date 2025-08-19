//IMPL intDiv
method intDiv(n:int, d:int) returns (q:int, r:int)
requires n >= d && n >= 0 && d > 0 
ensures (d*q)+r == n && 0 <= q <= n/2 && 0 <= r < d
{
    /* code modified by LLM (iteration 3): use min to respect both division result and n/2 constraint */
    var normalQ := n / d;
    var maxAllowedQ := n / 2;
    
    q := if normalQ <= maxAllowedQ then normalQ else maxAllowedQ;
    r := n - d * q;
    
    /* code modified by LLM (iteration 3): adjust if r >= d by reducing q if possible */
    while r >= d && q > 0
        invariant (d*q)+r == n
        invariant 0 <= q <= n/2
        invariant r >= 0
        decreases q
    {
        q := q - 1;
        r := r + d;
    }
}