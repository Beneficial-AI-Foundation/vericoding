function digitSum(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then 0
  else (n % 10) + digitSum(n / 10)
}

// <vc-helpers>
lemma digitSumNonNegative(x: int)
  requires x >= 0
  ensures digitSum(x) >= 0
  decreases x
{
  if x > 0 {
    digitSumNonNegative(x / 10);
  }
}

lemma digitSumUpperBound(x: int)
  requires x >= 0
  ensures digitSum(x) <= x
  decreases x
{
  if x > 0 {
    digitSumUpperBound(x / 10);
    assert digitSum(x) == (x % 10) + digitSum(x / 10);
    assert digitSum(x / 10) <= x / 10;
    var sum := (x % 10) + digitSum(x / 10);
    if x >= 10 {
      assert x % 10 <= 9;
      assert 9 + (x / 10) <= x;
    } else {
      assert x < 10;
      assert x % 10 == x;
    }
  }
}

lemma digitSumPositiveForXGe10(x: int)
  requires x >= 10
  ensures digitSum(x) > 0
  decreases x
{
  digitSumNonNegative(x / 10);
}

predicate ValidSolution(x: int, n: int) 
{
  x > 0 && x * x + digitSum(x) * x == n
}

lemma quadraticGrowth(x: int, n: int)
  requires x >= 1
  requires n >= 1
  ensures x * x + digitSum(x) * x >= x * x
  decreases x
{
  digitSumNonNegative(x);
}

lemma monotonicGrowth(x: int)
  requires x >= 1
  ensures x * x + digitSum(x) * x <= (x+1) * (x+1) + digitSum(x+1) * (x+1)
{
  digitSumNonNegative(x);
  digitSumNonNegative(x+1);
  
  // Base case for the inequality
  var left := x * x + digitSum(x) * x;
  var right := (x+1) * (x+1) + digitSum(x+1) * (x+1);
  
  // The function grows at least as fast as x² which is strictly increasing
  assert (x+1)*(x+1) > x*x;
  assert digitSum(x+1) >= 0;
  
  // For x >= 1, (x+1)² + 0*(x+1) > x² + digitSum(x)*x since digitSum(x) <= x
  digitSumUpperBound(x);
  assert digitSum(x) <= x;
  
  // x² + x² = 2x² which is less than (x+1)² for x >= 2
  if x >= 2 {
    assert 2*x*x < (x+1)*(x+1);
  }
  
  // Handle x == 1 case separately
  if x == 1 {
    assert left == 1*1 + digitSum(1)*1;
    assert digitSum(1) == 1;
    assert left == 2;
    assert right == 4 + digitSum(2)*2;
    assert digitSum(2) == 2;
    assert right == 8;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
  requires n >= 1
  ensures n == 1 ==> result == -1
  ensures n > 1 && result > 0 ==> result * result + digitSum(result) * result == n
  ensures n > 1 && result > 0 ==> forall y :: y > 0 && y < result ==> y * y + digitSum(y) * y != n
  ensures n > 1 && result == -1 ==> forall x :: x > 0 ==> x * x + digitSum(x) * x != n
  ensures result == -1 || result > 0
// </vc-spec>
// <vc-code>
{
  if n == 1 {
    result := -1;
    return;
  }
  
  var x := 1;
  result := -1;
  
  while x * x <= n
    invariant 1 <= x
    invariant result == -1
    invariant forall y :: 1 <= y < x ==> y * y + digitSum(y) * y != n
    decreases n - x
  {
    var f := x * x + digitSum(x) * x;
    
    if f == n {
      result := x;
      return;
    } 
    
    if f > n {
      break;
    }
    
    x := x + 1;
  }
  
  // Prove no solution exists for larger values
  ghost var y_max := x;
  assert forall y :: y >= y_max ==> {
    digitSumNonNegative(y);
    y * y + digitSum(y) * y >= y * y;
    y * y >= y_max * y_max;
    y_max * y_max > n || f > n;
    y * y + digitSum(y) * y > n
  };
}
// </vc-code>

