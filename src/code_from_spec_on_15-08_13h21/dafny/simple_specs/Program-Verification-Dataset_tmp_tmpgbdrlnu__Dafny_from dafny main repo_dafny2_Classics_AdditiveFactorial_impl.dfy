ghost function Factorial(n: nat): nat
{
 if n == 0 then 1 else n * Factorial(n-1)
}


//IMPL SPEC
method AdditiveFactorial(n: nat) returns (u: nat)
 ensures u == Factorial(n)
{
    if n == 0 {
        u := 1;
        return;
    }
    
    u := 1;
    var i := 1;
    
    while i <= n
        invariant 1 <= i <= n + 1
        invariant u == Factorial(i - 1)
    {
        var temp := u;
        var j := 1;
        /* code modified by LLM (iteration 1): Initialize u to temp instead of 0 to satisfy loop invariant on entry */
        u := temp;
        
        while j < i
            invariant 0 <= j <= i
            invariant u == j * temp
        {
            u := u + temp;
            j := j + 1;
        }
        
        i := i + 1;
    }
}