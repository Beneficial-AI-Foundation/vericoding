//ATOM
function F(n: nat): nat { if n <= 2 then n else F(n-1) + F(n-3)}

//IMPL 
method calcF(n: nat) returns (res: nat) 
 ensures res == F(n) 
{
    if n <= 2 {
        return n;
    }
    
    var a, b, c := 0, 1, 2;
    var i := 3;
    
    while i <= n
        invariant 3 <= i <= n + 1
        invariant a == F(i-3)
        invariant b == F(i-2) 
        invariant c == F(i-1)
    {
        var next := c + a;
        a, b, c := b, c, next;
        i := i + 1;
    }
    
    return c;
}