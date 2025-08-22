//IMPL Mult
method Mult(x:nat, y:nat) returns (r:nat)
ensures r == x * y
{
    var m := x;
    var n := y;
    r := 0;
    
    /* code modified by LLM (iteration 1): added proper loop invariant to establish the relationship between variables and the postcondition */
    while m > 0
        invariant m * n + r == x * y
        invariant m >= 0
        decreases m
    {
        r := r + n;
        m := m - 1;
    }
}