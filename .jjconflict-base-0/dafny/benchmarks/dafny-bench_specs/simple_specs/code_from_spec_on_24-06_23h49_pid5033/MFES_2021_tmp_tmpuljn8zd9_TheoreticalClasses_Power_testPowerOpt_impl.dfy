//ATOM

// Recursive version, imperative, with time and space complexity O(log n).
method powerOpt(x: real, n: nat) returns (p : real)
 ensures p == power(x, n)
{
  p := 0.0;
  assume p == power(x, n);
  return p;
}


//ATOM

// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
function power(x: real, n: nat) : real
{
  if n == 0 then 1.0 else x * power(x, n-1)
}


//IMPL testPowerOpt

method testPowerOpt(){
  /* code modified by LLM (iteration 1): Fixed method call syntax - methods return values through out parameters, not return expressions */
  var result1 := powerOpt(2.0, 3);
  var result2 := powerOpt(5.0, 0);
  var result3 := powerOpt(1.0, 10);
}