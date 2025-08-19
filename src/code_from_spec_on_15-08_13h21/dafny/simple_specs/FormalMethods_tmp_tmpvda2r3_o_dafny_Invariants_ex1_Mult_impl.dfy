method Mult(x:nat, y:nat) returns (r:nat)
ensures r == x * y
{
    var m := x;
    var n := y;
    r := 0;
    
    while m > 0
        invariant m >= 0
        invariant m*n + r == x*y
        decreases m
    {
        m := m - 1;
        r := r + n;
    }
    
    /* code modified by LLM (iteration 3): Removed redundant assertions and rely on loop invariant to establish m >= 0 */
    assert m*n + r == x*y;
    assert m == 0;
}