//ATOM
// recursive definition of factorial
function Factorial(n: nat): nat {
 if n == 0 then 1 else n * Factorial(n - 1)
}

//IMPL iterative implementation of factorial
method IterativeFactorial(n: nat) returns (result: nat)
 ensures result == Factorial(n)
{
    result := 1;
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant result == Factorial(i)
    {
        i := i + 1;
        result := result * i;
    }
}