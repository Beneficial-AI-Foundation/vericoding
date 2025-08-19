//ATOM

// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
function power(x: real, n: nat) : real
{
  if n == 0 then 1.0 else x * power(x, n-1)
}

//IMPL 

// Iterative version, imperative, with time complexity O(n) and space complexity O(1).
method powerIter(x: real, n: nat) returns (p : real)
 ensures p == power(x, n)
{
  /* code modified by LLM (iteration 1): removed invalid text at beginning of file and added proper loop body */
  p := 1.0;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant p * power(x, n - i) == power(x, n)
  {
    p := p * x;
    i := i + 1;
  }
}