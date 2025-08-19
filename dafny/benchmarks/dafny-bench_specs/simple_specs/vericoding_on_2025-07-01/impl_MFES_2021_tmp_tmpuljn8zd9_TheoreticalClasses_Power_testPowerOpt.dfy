//ATOM

// Recursive version, imperative, with time and space complexity O(log n).
method powerOpt(x: real, n: nat) returns (p : real)
 ensures p == power(x, n)
{
  p := 0.0;
  assume p ==> power(x, n);
  return p;
}

//ATOM

// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
function power(x: real, n: nat) : real
{
  if n == 0 then 1.0 else x * power(x, n-1)
}


// SPEC

method testPowerOpt(){
}