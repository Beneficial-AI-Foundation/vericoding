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
  p := 1.0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant p == power(x, i)
  {
    p := p * x;
    i := i + 1;
  }
}


//IMPL 

// A simple test case to make sure the specification is adequate.
method testPowerIter()
{
  var result := powerIter(2.0, 3);
  assert result == 8.0;
  
  var result2 := powerIter(5.0, 0);
  assert result2 == 1.0;
  
  var result3 := powerIter(3.0, 2);
  assert result3 == 9.0;
}