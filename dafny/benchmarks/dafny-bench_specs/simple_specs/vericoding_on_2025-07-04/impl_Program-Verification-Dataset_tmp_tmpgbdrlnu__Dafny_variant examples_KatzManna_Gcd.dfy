//IMPL 
method Gcd(x1: int, x2: int)
 requires 1 <= x1 && 1 <= x2
{
    var a := x1;
    var b := x2;
    
    /* code modified by LLM (iteration 1): Fixed decreases clause to use absolute value of b to handle negative remainders */
    while b != 0
        decreases if b >= 0 then b else -b
    {
        var temp := b;
        b := a % b;
        a := temp;
    }
}