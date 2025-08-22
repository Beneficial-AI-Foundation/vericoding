//IMPL 
method Mult(x:nat, y:nat) returns (r:nat)
ensures r == x * y
{
    var m := x;
    var n := y;
    r := 0;
    
    /* code modified by LLM (iteration 1): Added explicit loop invariant to ensure verification */
    while m > 0
        invariant m * n + r == x * y
        invariant m >= 0
        decreases m
    {
        /* code modified by LLM (iteration 1): Reordered operations to make verification clearer */
        r := r + n;
        m := m - 1;
    }
}