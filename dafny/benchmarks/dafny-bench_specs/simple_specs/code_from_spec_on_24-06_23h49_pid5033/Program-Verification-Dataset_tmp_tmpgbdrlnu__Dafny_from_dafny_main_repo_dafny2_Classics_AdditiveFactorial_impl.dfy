//ATOM
// RUN: %testDafnyForEachResolver "%s" -- --warn-deprecation:false


// A version of Turing's additive factorial program [Dr. A. Turing, "Checking a large routine",
// In "Report of a Conference of High Speed Automatic Calculating Machines", pp. 67-69, 1949].

ghost function Factorial(n: nat): nat
{
 if n == 0 then 1 else n * Factorial(n-1)
}


//IMPL AdditiveFactorial

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
        u := u * i;
        i := i + 1;
    }
}