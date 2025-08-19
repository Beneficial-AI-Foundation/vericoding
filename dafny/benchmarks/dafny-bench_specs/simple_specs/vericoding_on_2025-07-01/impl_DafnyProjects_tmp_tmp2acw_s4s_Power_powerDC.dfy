//ATOM

// Recursive definition of x^n in functional style, with time and space complexity O(n).
function power(x: real, n: nat) : real {
  if n == 0 then 1.0 else x * power(x, n-1)
}


//IMPL

// Computation of x^n in time and space O(log n).
method powerDC(x: real, n: nat) returns (p : real)
 ensures p == power(x, n)
{
  if n == 0 {
    p := 1.0;
  } else if n % 2 == 0 {
    var half := powerDC(x, n / 2);
    p := half * half;
  } else {
    var half := powerDC(x, (n - 1) / 2);
    p := x * half * half;
  }
}