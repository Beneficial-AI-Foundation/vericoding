//ATOM
// Computation of x^n in time and space O(log n).
method powerDC(x: real, n: nat) returns (p : real)
 ensures p == power(x, n)
{
  /* code modified by LLM (iteration 1): Implemented efficient divide-and-conquer algorithm */
  if n == 0 {
    p := 1.0;
  } else if n % 2 == 0 {
    var half := powerDC(x, n / 2);
    p := half * half;
  } else {
    var temp := powerDC(x, n - 1);
    p := x * temp;
  }
}

//ATOM
// Recursive definition of x^n in functional style, with time and space complexity O(n).
function power(x: real, n: nat) : real {
  if n == 0 then 1.0 else x * power(x, n-1)
}

//IMPL
// A few test cases (checked statically by Dafny).
method testPowerDC() {
  /* code modified by LLM (iteration 1): Fixed implementation to properly call powerDC and verify results */
  var result1 := powerDC(2.0, 3);
  var result2 := powerDC(5.0, 2);
  var result3 := powerDC(1.0, 100);
  
  /* code modified by LLM (iteration 1): Added assertions that should hold due to powerDC's postcondition */
  assert result1 == power(2.0, 3);
  assert result2 == power(5.0, 2);
  assert result3 == power(1.0, 100);
}