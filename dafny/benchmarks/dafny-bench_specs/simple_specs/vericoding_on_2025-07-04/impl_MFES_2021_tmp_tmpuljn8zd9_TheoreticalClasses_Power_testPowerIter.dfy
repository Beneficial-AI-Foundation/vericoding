//ATOM

// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
function power(x: real, n: nat) : real
{
  if n == 0 then 1.0 else x * power(x, n-1)
}


//ATOM

// Iterative version, imperative, with time complexity O(n) and space complexity O(1).
method powerIter(x: real, n: nat) returns (p : real)
 ensures p == power(x, n)
{
  p := 0.0;
  assume p == power(x, n);
  return p;
}


//IMPL 

// A simple test case to make sure the specification is adequate.
method testPowerIter()
{
  var result := powerIter(2.0, 3);
  assert result == power(2.0, 3);
  
  var result2 := powerIter(5.0, 0);
  assert result2 == power(5.0, 0);
  assert result2 == 1.0;
  
  var result3 := powerIter(1.0, 10);
  assert result3 == power(1.0, 10);
  assert result3 == 1.0;
}