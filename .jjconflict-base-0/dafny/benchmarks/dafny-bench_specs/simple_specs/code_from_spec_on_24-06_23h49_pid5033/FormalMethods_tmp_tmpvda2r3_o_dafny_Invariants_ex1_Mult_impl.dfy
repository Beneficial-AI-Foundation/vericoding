//IMPL 
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
        /* code modified by LLM (iteration 4): Loop body that decrements m and adds n to r, preserving invariant */
        m := m - 1;
        r := r + n;
    }
}