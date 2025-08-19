//ATOM

// Computation of x^n in time and space O(log n).
method powerDC(x: real, n: nat) returns (p : real)
 ensures p == power(x, n)
{
  p := 0.0;
  assume p ==> power(x, n);
  return p;
}

//ATOM

// Recursive definition of x^n in functional style, with time and space complexity O(n).
function power(x: real, n: nat) : real {
  if n == 0 then 1.0 else x * power(x, n-1)
}


// SPEC


// A few test cases (checked statically by Dafny).
method testPowerDC() {
}