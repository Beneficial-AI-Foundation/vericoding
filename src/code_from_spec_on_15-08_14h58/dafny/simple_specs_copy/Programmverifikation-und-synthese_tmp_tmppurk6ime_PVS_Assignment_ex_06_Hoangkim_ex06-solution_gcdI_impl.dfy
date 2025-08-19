/* code modified by LLM (iteration 4): fixed decreases clause to use max of arguments */
ghost function gcd'(x:int,y:int):int
 requires x > 0 && y > 0
 decreases if x >= y then x else y, if x >= y then y else x
{
 if x==y then x
 else if x > y then gcd'(x-y,y)
 else gcd'(y,x)
}

//IMPL
/* code modified by LLM (iteration 4): complete implementation with proper loop invariants and assertions */
method gcdI(m:int, n:int) returns (d:int)
 requires m > 0 && n > 0
 ensures  d == gcd'(m,n) 
{
    var a := m;
    var b := n;
    
    while a != b
        invariant a > 0 && b > 0
        invariant gcd'(a, b) == gcd'(m, n)
        decreases a + b
    {
        if a > b {
            /* code modified by LLM (iteration 4): added assertion to help prove invariant maintenance */
            assert gcd'(a, b) == gcd'(a - b, b);
            a := a - b;
        } else {
            /* code modified by LLM (iteration 4): added assertions to help prove invariant maintenance when b > a */
            assert gcd'(a, b) == gcd'(b, a);
            assert gcd'(b, a) == gcd'(b - a, a);
            assert gcd'(b - a, a) == gcd'(a, b - a);
            b := b - a;
        }
    }
    
    d := a;
}