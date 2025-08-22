// recursive definition of factorial
// ATOM 
// recursive definition of factorial
function Factorial(n: nat): nat {
  if n == 0 then 1 else n * Factorial(n - 1)
}


// iterative implementation of factorial
// SPEC 

// iterative implementation of factorial
method IterativeFactorial(n: nat) returns (result: nat)
  ensures result == Factorial(n)
{
}




