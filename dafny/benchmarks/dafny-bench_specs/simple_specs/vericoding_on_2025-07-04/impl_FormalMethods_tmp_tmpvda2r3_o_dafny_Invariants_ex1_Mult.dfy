//IMPL
method Mult(x:nat, y:nat) returns (r:nat)
ensures r == x * y
{
    var m := x;
    var n := y;
    r := 0;
    
    while m > 0
        invariant m * n + r == x * y
        invariant n == y
        decreases m
    {
        /* code modified by LLM (iteration 4): restructured to help Dafny verify invariant preservation */
        assert m > 0;
        assert m * n + r == x * y;
        assert n == y;
        
        r := r + n;
        m := m - 1;
        
        /* code modified by LLM (iteration 4): help Dafny see that invariant is preserved */
        assert (m + 1) * n + (r - n) == x * y;
        assert m * n + n + r - n == x * y;
        assert m * n + r == x * y;
    }
    
    /* code modified by LLM (iteration 4): help establish postcondition from loop invariant */
    assert m == 0;
    assert m * n + r == x * y;
    assert 0 * n + r == x * y;
    assert r == x * y;
}