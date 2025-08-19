method Mult(x:nat, y:nat) returns (r:nat)
ensures r == x * y
{
    var m := x;
    var n := y;
    r := 0;
    
    while m > 0
        invariant m * n + r == x * y
        decreases m
    {
        m := m - 1;
        r := r + n;
    }
    
    /* code modified by LLM (iteration 1): Added assertion to help Dafny prove postcondition */
    assert m == 0;
    assert m * n + r == x * y;
    assert 0 * n + r == x * y;
    assert r == x * y;
}