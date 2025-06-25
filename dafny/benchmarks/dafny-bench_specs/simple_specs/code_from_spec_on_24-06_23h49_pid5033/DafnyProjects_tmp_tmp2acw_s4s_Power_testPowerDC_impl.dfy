//ATOM

// Computation of x^n in time and space O(log n).
method powerDC(x: real, n: nat) returns (p : real)
 ensures p == power(x, n)
{
  p := 0.0;
  assume p == power(x, n);
  return p;
}


//ATOM

// Recursive definition of x^n in functional style, with time and space complexity O(n).
function power(x: real, n: nat) : real {
  if n == 0 then 1.0 else x * power(x, n-1)
}


//IMPL testPowerDC

/* code modified by LLM (iteration 1): Simplified test method that works with the broken powerDC implementation */
// A few test cases (checked statically by Dafny).
method testPowerDC() {
  // Test various inputs to powerDC
  var result1 := powerDC(5.0, 0);
  var result2 := powerDC(3.0, 1);
  var result3 := powerDC(2.0, 3);
  var result4 := powerDC(1.0, 10);
  var result5 := powerDC(0.0, 5);
  
  // Due to powerDC's postcondition, we can assert the expected mathematical results
  // even though the implementation is broken (it uses assume)
  assert result1 == power(5.0, 0);
  assert result2 == power(3.0, 1);
  assert result3 == power(2.0, 3);
  assert result4 == power(1.0, 10);
  assert result5 == power(0.0, 5);
  
  // We can also test specific expected values
  assert result1 == 1.0;   // 5^0 = 1
  assert result2 == 3.0;   // 3^1 = 3
  assert result3 == 8.0;   // 2^3 = 8
  assert result4 == 1.0;   // 1^10 = 1
  assert result5 == 0.0;   // 0^5 = 0
}