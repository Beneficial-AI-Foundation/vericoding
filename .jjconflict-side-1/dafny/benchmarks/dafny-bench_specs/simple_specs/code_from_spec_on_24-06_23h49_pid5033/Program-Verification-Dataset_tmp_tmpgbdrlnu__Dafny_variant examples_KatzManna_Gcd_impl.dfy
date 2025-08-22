//IMPL 
method Gcd(x1: int, x2: int) returns (result: int)
 requires 1 <= x1 && 1 <= x2
 ensures result > 0
{
    var a := x1;
    var b := x2;
    
    /* code modified by LLM (iteration 2): fixed decreases clause to use b which decreases to 0, and strengthened invariant */
    while b != 0
        decreases b
        invariant a > 0 && b >= 0
    {
        var temp := b;
        b := a % b;
        a := temp;
    }
    
    /* code modified by LLM (iteration 2): return statement remains the same */
    result := a;
}